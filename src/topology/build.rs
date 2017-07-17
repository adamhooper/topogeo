use std::collections::HashMap;
use std::collections::hash_map::Entry;

use geo::{WindingOrder, Edge, Point, Ring, Region};
use super::types::{Topology, TopoEdge, TopoRegion, TopoRing, TopoEdgeId, TopoRingId, TopoRegionId, NULL_ID, DirectedEdge, Direction};

pub struct TopologyBuilder<Data> {
    regions: Vec<TopoRegion<Data>>,
    rings: Vec<TopoRing>,
    edges: Vec<TopoEdge>,

    // HashMap's Entry API lets us insert-or-get the key
    edge_ids: HashMap<Vec<Point>, TopoEdgeId>,
}

impl<Data> TopologyBuilder<Data>
{
    pub fn new() -> TopologyBuilder<Data> {
        TopologyBuilder::<Data> {
            regions: vec!(),
            rings: vec!(),
            edges: vec!(),
            edge_ids: HashMap::new(),
        }
    }

    pub fn add_region(&mut self, region: Region<Data>) {
        let Region { data, outer_rings, inner_rings } = region;
        let region_id = self.regions.len() as TopoRegionId;

        let outer_ring_ids = self.add_rings(region_id, &outer_rings[..]);

        if outer_ring_ids.len() > 0 {
            let inner_ring_ids = self.add_rings(region_id, &inner_rings[..]);
            self.regions.push(TopoRegion {
                data: data,
                outer_ring_ids: outer_ring_ids,
                inner_ring_ids: inner_ring_ids,
            });
        }
    }

    /// Adds to self.edges, self.edge_ids and self.rings; returns IDs.
    ///
    /// Eliminates any Rings that have zero area. Beware: this may return an
    /// empty Vec.
    fn add_rings(&mut self, region_id: TopoRegionId, rings: &[Ring]) -> Box<[TopoRingId]> {
        rings.into_iter()
            .map(|r| self.add_ring(region_id, r))
            .filter(|&r| r != NULL_ID)
            .collect::<Vec<TopoRingId>>()
            .into_boxed_slice()
    }

    /// Adds to self.edges, self.edge_ids and self.rings; returns an ID.
    ///
    /// Returns NULL_ID if the given ring is invalid (area == 0).
    fn add_ring(&mut self, region_id: TopoRegionId, ring: &Ring) -> TopoRingId {
        if ring.area2() == 0 {
            return NULL_ID;
        }

        let ring_id: TopoRingId = self.rings.len() as TopoRingId;

        let directed_edges: Vec<DirectedEdge> = ring.edges().iter()
            .flat_map(|e| self.add_directed_edge(ring_id, e))
            .collect();

        self.rings.push(TopoRing {
            directed_edges: directed_edges.into_boxed_slice(),
            region_id: region_id,
        });
        ring_id
    }

    /// Returns a DirectedEdge, building an Edge if it is missing.
    ///
    /// Returns None when given an empty (zero-length) edge.
    fn add_directed_edge(&mut self, ring_id: TopoRingId, edge: &Edge) -> Option<DirectedEdge> {
        let mut points = edge.0.to_vec();

        if points.len() < 2 || points.iter().all(|&p| p == points[0]) {
            // zero-length edge
            return None
        }

        let p1 = points[0];
        let p2 = points[points.len() - 1];

        let direction = if p1 < p2 || (p1 == p2 && Ring::Points(points.clone().into_boxed_slice()).winding_order() == WindingOrder::Clockwise) {
            Direction::Forward
        } else {
            points.reverse();
            Direction::Backward
        };

        let next_id = self.edges.len() as TopoEdgeId;

        let edge_id: TopoEdgeId = match self.edge_ids.entry(points) {
            Entry::Occupied(entry) => {
                let ret = *entry.get();
                self.edges[ret as usize].ring2_id = ring_id;
                ret
            }
            Entry::Vacant(entry) => {
                self.edges.push(TopoEdge {
                    points: entry.key().clone().into_boxed_slice(),
                    ring1_id: ring_id,
                    ring2_id: NULL_ID,
                });
                entry.insert(next_id);
                next_id
            }
        };

        Some(DirectedEdge { edge_id: edge_id, direction: direction })
    }

    pub fn into_topology(self) -> Topology<Data> {
        Topology {
            regions: self.regions.into_boxed_slice(),
            rings: self.rings.into_boxed_slice(),
            edges: self.edges.into_boxed_slice(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_region() {
        let mut builder = TopologyBuilder::<u32>::new();

        builder.add_region(Region::<u32> {
            data: 42,
            outer_rings: vec![
                Ring::Points(vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ].into_boxed_slice()),
                Ring::Points(vec![ Point(10, 10), Point(20, 10), Point(10, 20), Point(10, 10) ].into_boxed_slice()),
            ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice(),
        });

        let topology = builder.into_topology();

        assert_eq!(1, topology.regions.len());
        assert_eq!(6, topology.edges.len());
    }

    #[test]
    fn share_point() {
        let mut builder = TopologyBuilder::<()>::new();

        // *--*--*
        // | / \ |
        // |/   \|
        // *     *
        builder.add_region(Region::<()> {
            data: (),
            outer_rings: vec![
                Ring::Points(vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ].into_boxed_slice()),
                Ring::Points(vec![ Point(2, 1), Point(3, 1), Point(3, 2), Point(2, 1) ].into_boxed_slice()),
            ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice()
        });

        let topology = builder.into_topology();

        assert_eq!(1, topology.regions.len());
        assert_eq!(6, topology.edges.len());
    }

    #[test]
    fn share_edge() {
        let mut builder = TopologyBuilder::<()>::new();

        // *--*
        // | /|
        // |/ |
        // *--*
        builder.add_region(Region::<()> {
            data: (),
            outer_rings: vec![
                Ring::Points(vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ].into_boxed_slice()),
                Ring::Points(vec![ Point(2, 1), Point(2, 2), Point(1, 2), Point(2, 1) ].into_boxed_slice()),
            ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice()
        });

        let topology = builder.into_topology();

        assert_eq!(1, topology.regions.len());
        assert_eq!(5, topology.edges.len());

        assert_eq!(
            topology.rings[0].directed_edges[1].edge_id,
            topology.rings[1].directed_edges[2].edge_id
        );
        assert_eq!(Direction::Backward, topology.rings[0].directed_edges[1].direction);
        assert_eq!(Direction::Forward, topology.rings[1].directed_edges[2].direction);
    }

    #[test]
    fn share_edge_two_regions() {
        let mut builder = TopologyBuilder::<()>::new();

        builder.add_region(Region::<()> {
            data: (),
            outer_rings: vec![ Ring::Points(vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ].into_boxed_slice()) ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice(),
        });

        builder.add_region(Region::<()> {
            data: (),
            outer_rings: vec![ Ring::Points(vec![ Point(2, 1), Point(2, 2), Point(1, 2), Point(2, 1) ].into_boxed_slice()) ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice(),
        });

        let topology = builder.into_topology();

        assert_eq!(5, topology.edges.len());
        assert_eq!(
            topology.rings[0].directed_edges[1].edge_id,
            topology.rings[1].directed_edges[2].edge_id
        );
    }

    #[test]
    fn inner_hole() {
        let mut builder = TopologyBuilder::<()>::new();

        builder.add_region(Region::<()> {
            data: (),
            outer_rings: vec![ Ring::Points(vec![ Point(0, 0), Point(3, 0), Point(0, 3), Point(0, 0) ].into_boxed_slice()) ].into_boxed_slice(),
            inner_rings: vec![ Ring::Points(vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ].into_boxed_slice()) ].into_boxed_slice(),
        });

        let topology = builder.into_topology();

        assert_eq!(6, topology.edges.len());
    }

    #[test]
    fn filter_zero_edge() {
        let mut builder = TopologyBuilder::<()>::new();

        builder.add_region(Region::<()> {
            data: (),
            outer_rings: vec![ Ring::Points(vec![ Point(0, 0), Point(1, 0), Point(1, 0), Point(0, 1), Point(0, 0) ].into_boxed_slice()) ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice(),
        });

        let topology = builder.into_topology();

        assert_eq!(3, topology.edges.len());
    }

    #[test]
    fn filter_zero_ring() {
        let mut builder = TopologyBuilder::<()>::new();

        builder.add_region(Region::<()> {
            data: (),
            outer_rings: vec![
                Ring::Points(vec![ Point(0, 0), Point(1, 0), Point(0, 1), Point(0, 0) ].into_boxed_slice()),
                Ring::Points(vec![ Point(1, 1), Point(1, 2), Point(1, 3), Point(1, 1) ].into_boxed_slice()),
            ].into_boxed_slice(),
            inner_rings: vec![ ].into_boxed_slice(),
        });

        let topology = builder.into_topology();
        assert_eq!(1, topology.regions[0].outer_ring_ids.len());
    }

    #[test]
    fn filter_zero_region() {
        let mut builder = TopologyBuilder::<()>::new();

        builder.add_region(Region::<()> {
            data: (),
            outer_rings: vec![
                Ring::Points(vec![ Point(1, 1), Point(1, 2), Point(1, 3), Point(1, 1) ].into_boxed_slice()),
            ].into_boxed_slice(),
            inner_rings: vec![ ].into_boxed_slice(),
        });

        let topology = builder.into_topology();
        assert_eq!(0, topology.regions.len());
    }
}
