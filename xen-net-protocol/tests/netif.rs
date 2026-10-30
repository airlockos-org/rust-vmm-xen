//! Native ABI examples and hostile peer lifetimes through the public core API.
use xen_net_protocol::{
    Invalid, Receive,
    loans::{Completion, Direction, Page},
    queue::Front,
};

/// Byte examples follow Xen's public netif ABI, independently of the encoders.
#[test]
fn native_descriptors_and_mutable_peer_snapshot() {
    assert_eq!(
        xen_net_protocol::tx_request(0x44332211, 0x6655, 1500),
        Some([0x11, 0x22, 0x33, 0x44, 0, 0, 0, 0, 0x55, 0x66, 0xdc, 0x05])
    );
    assert_eq!(
        xen_net_protocol::rx_request(0x44332211, 0x6655),
        [0x55, 0x66, 0, 0, 0x11, 0x22, 0x33, 0x44]
    );
    assert!(xen_net_protocol::tx_request(1, 0, 4097).is_none());
    assert!(xen_net_protocol::tx_request(1, 0, 0).is_none());
    assert_eq!(
        xen_net_protocol::tx_response(&[1, 0, 0xfe, 0xff], 1),
        Ok(false)
    );
    assert_eq!(
        xen_net_protocol::tx_response(&[2, 0, 0, 0], 1),
        Err(Invalid::Identity)
    );
    assert_eq!(
        xen_net_protocol::tx_response(&[1, 0, 1, 0], 1),
        Err(Invalid::Status)
    );

    let mut peer = [7, 0, 2, 0, 1, 0, 0xfe, 0x0f];
    let snapshot = peer;
    let Receive::Packet(frame) = xen_net_protocol::rx_response(&snapshot, 7).unwrap() else {
        panic!("packet expected");
    };
    peer.fill(0xff);
    assert_eq!(frame.len(), 4094);
    assert_eq!(frame.byte(4093), Some(4095));
    assert_eq!(frame.byte(4094), None);
    assert!(xen_net_protocol::rx_response(&peer, 7).is_err());
    assert!(matches!(
        xen_net_protocol::rx_response(&[7, 0, 3, 0, 0, 0, 0xfe, 15], 7),
        Err(Invalid::Bounds)
    ));
    assert!(matches!(
        xen_net_protocol::rx_response(&[7, 0, 0, 0, 2, 0, 64, 0], 7),
        Err(Invalid::Flags)
    ));
}

/// Full ring backpressure, response overrun and index ownership are distinct.
#[test]
fn bounded_ring_wraps_and_peer_counter_corruption() {
    let mut ring = Front::tx();
    let mut produced = 0;
    let mut consumed = 0;
    for _ in 0..3 {
        for _ in 0..256 {
            let slot = ring.request(produced).unwrap().unwrap();
            assert_eq!(slot.len(), 12);
            assert!(slot.byte(11).unwrap() < 4096);
            assert_eq!(slot.byte(12), None);
            produced = slot.published();
            assert!(ring.posted(slot));
        }
        assert!(ring.request(produced).unwrap().is_none());
        assert!(ring.response(produced, produced + 1).is_err());
        for _ in 0..256 {
            let slot = ring.response(produced, produced).unwrap().unwrap();
            consumed = slot.published();
            assert!(ring.consumed_response(slot));
        }
        assert_eq!(consumed, produced);
        assert!(ring.response(produced, produced).unwrap().is_none());
    }
    assert!(ring.request(produced + 1).is_err());
    assert!(ring.response(produced + 1, produced).is_err());
    assert_eq!(xen_store_protocol::ring::next_index(u32::MAX, 1), 0);
    assert!(xen_store_protocol::ring::event_needed(u32::MAX, 0, 0));
    assert!(!xen_store_protocol::ring::event_needed(u32::MAX, 0, 1));
}

/// Peer completion does not release ownership, and one stalled page has no
/// authority to stall another owner's finite polling/reclamation operations.
#[test]
fn independent_loans_and_expired_grant_retention() {
    let mut stalled = Page::new(Direction::Transmit);
    assert!(stalled.offer(100));
    assert!(!stalled.offer(200));
    assert!(stalled.complete(Completion::Transmit(true), 200));
    assert!(!stalled.complete(Completion::Transmit(false), 200));
    assert!(stalled.reclaim(false).is_none());
    assert!(!stalled.reusable());
    assert!(!stalled.expire(99));

    let mut healthy = Page::new(Direction::Receive);
    assert!(healthy.offer(u64::MAX));
    assert!(!healthy.expire(1_000_000));
    let completion = xen_net_protocol::rx_response(&[1, 0, 2, 0, 0, 0, 64, 0], 1).unwrap();
    assert!(healthy.complete(Completion::Receive(completion), 1_000_100));
    assert!(healthy.reclaim(false).is_none());
    let Some(Completion::Receive(Receive::Packet(frame))) = healthy.reclaim(true) else {
        panic!("reclaimed RX expected");
    };
    assert_eq!(frame.byte(0), Some(2));
    assert_eq!(frame.len(), 64);
    assert!(healthy.reusable());

    assert!(stalled.expire(100));
    assert!(stalled.reclaim(true).is_none());
    assert!(!stalled.offer(300));
    assert!(!stalled.reusable());
    healthy.quarantine();
    assert!(!healthy.reusable());
}

/// A parsed peer claim cannot change caller authorization or redirect the
/// backend lookup; reciprocal paths bind the same toolstack-owned frontend.
#[test]
fn exact_toolstack_links() {
    use xen_net_protocol::identity::{backend_linked, domain_matches, frontend_linked};
    assert!(domain_matches(b"0", 0));
    assert!(!domain_matches(b"00", 0));
    assert!(!domain_matches(b"32752", 32752));
    assert!(!domain_matches(b"1", 0));
    assert!(backend_linked(
        0,
        b"0",
        b"42",
        b"/local/domain/0/backend/vif/42/0"
    ));
    assert!(!backend_linked(
        0,
        b"1",
        b"42",
        b"/local/domain/1/backend/vif/42/0"
    ));
    assert!(!backend_linked(
        0,
        b"0",
        b"42",
        b"/local/domain/0/backend/vif/42/1"
    ));
    assert!(!backend_linked(
        0,
        b"0",
        b"42/../1",
        b"/local/domain/0/backend/vif/42/../1/0"
    ));
    assert!(frontend_linked(b"42", b"/local/domain/42/device/vif/0"));
    assert!(!frontend_linked(b"42", b"/local/domain/41/device/vif/0"));
}

/// Ambiguous opening/cleanup outcomes are retained, not silently replayed.
#[test]
fn explicit_lifecycle_and_wrong_direction_completion() {
    use xen_net_protocol::bus::Life;
    let mut life = Life::new();
    assert!(!life.usable());
    assert!(life.begin());
    assert!(!life.begin());
    assert!(!life.connected(b"4", false));
    assert!(!life.usable());
    assert!(!life.begin());
    assert!(life.close());
    assert!(!life.close());
    assert!(!life.released(false));
    life.fail();
    assert!(!life.close());
    assert!(!life.begin());

    let mut good = Life::new();
    assert!(good.begin());
    assert!(good.connected(b"4", true));
    assert!(good.usable());
    assert!(good.close());
    assert!(!good.usable());
    assert!(good.released(true));
    assert!(!good.begin());
    assert!(!good.close());

    let mut receive = Page::new(Direction::Receive);
    assert!(receive.offer(u64::MAX));
    assert!(!receive.complete(Completion::Transmit(true), 100));
    assert!(receive.awaiting());
    assert!(receive.reclaim(true).is_none());
}
