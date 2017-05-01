use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::ptr;

use geo::{WindingOrder, Edge, Point, Ring, Region};
use super::types::{Topology, TopoEdge, TopoRegion, TopoRing, DirectedEdge, Direction};

// Our "Id" types are array indices.
type EdgeId = usize;

#[derive(Debug)]
struct BuildRegion<Data> {
    data: Data,
    outer_rings: Vec<BuildRing>,
    inner_rings: Vec<BuildRing>,
}

#[derive(Debug)]
struct BuildRing(Vec<BuildDirectedEdge>);

#[derive(Debug)]
struct BuildDirectedEdge {
    edge_id: EdgeId,
    direction: Direction,
}

#[derive(Debug,Eq,PartialEq,Hash)]
struct BuildEdge(Vec<Point>);

fn build_ring_to_topo_ring_with_null_ptrs<Data>(edges: &Vec<TopoEdge<Data>>, build_ring: &BuildRing) -> TopoRing<Data> {
    let directed_edges: Vec<DirectedEdge<Data>> = build_ring.0.iter().map(|build_de| {
        DirectedEdge {
            edge: &edges[build_de.edge_id] as *const TopoEdge<Data>,
            direction: build_de.direction,
        }
    }).collect();

    TopoRing {
        directed_edges: directed_edges.into_boxed_slice(),
        region: ptr::null(),
    }
}

pub struct TopologyBuilder<Data> {
    regions: Vec<BuildRegion<Data>>,
    // HashMap's Entry API lets us insert-or-get the key
    edges: HashMap<BuildEdge, EdgeId>,
}

impl<Data> TopologyBuilder<Data>
{
    pub fn new() -> TopologyBuilder<Data> {
        TopologyBuilder::<Data> {
            regions: vec!(),
            edges: HashMap::new(),
        }
    }

    pub fn add_region(&mut self, region: Region<Data>) {
        let Region { data, outer_rings, inner_rings } = region;

        let build_outer_rings = self.build_rings(outer_rings);

        if build_outer_rings.len() > 0 {
            let build_inner_rings = self.build_rings(inner_rings);
            self.regions.push(BuildRegion {
                data: data,
                outer_rings: build_outer_rings,
                inner_rings: build_inner_rings,
            });
        }
    }

    /// Converts the given Rings to BuildRings.
    ///
    /// Side-effects: may add to self.edges.
    ///
    /// Eliminates any Rings that have zero area. Beware: this may return an
    /// empty Vec.
    fn build_rings(&mut self, rings: Box<[Ring]>) -> Vec<BuildRing> {
        rings.into_iter().flat_map(|r| self.build_ring(r)).collect()
    }

    /// Returns a Ring representing the input.
    ///
    /// Side-effect: may add to self.edges.
    ///
    /// Returns None if the given ring is invalid (area == 0).
    fn build_ring(&mut self, ring: &Ring) -> Option<BuildRing> {
        if ring.area2() == 0 {
            return None
        }

        let directed_edges: Vec<BuildDirectedEdge> = ring.edges().iter()
            .flat_map(|e| self.build_directed_edge(e))
            .collect();

        Some(BuildRing(directed_edges))
    }

    /// Returns a BuildDirectedEdge, building a BuildEdge if it is missing.
    fn build_directed_edge(&mut self, edge: &Edge) -> Option<BuildDirectedEdge> {
        let mut points = edge.0.to_vec();

        if points.len() < 2 || (points.len() == 2 && points[0] == points[1]) {
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

        let next_id = self.edges.len();

        let maybe_new_edge = BuildEdge(points);
        let edge_id: EdgeId = match self.edges.entry(maybe_new_edge) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                entry.insert(next_id);
                next_id
            }
        };

        Some(BuildDirectedEdge { edge_id: edge_id, direction: direction })
    }

    pub fn into_topology(self) -> Topology<Data> {
        // We can "sort" by id because we know the ids are <= self.edges.len():
        // just put each edge in its place.

        let mut edges_sort = Vec::<Option<TopoEdge<Data>>>::with_capacity(self.edges.len());
        for _ in 0 .. self.edges.len() {
            edges_sort.push(None)
        }
        for (build_edge, id) in self.edges {
            edges_sort[id] = Some(TopoEdge {
                points: build_edge.0.into_boxed_slice(),
                rings: [ ptr::null(); 2 ], // we'll fill these in later
            })
        }

        let edges: Vec<TopoEdge<Data>> = edges_sort.into_iter()
            .map(|o| o.expect("programming error: an Edge is missing from self.edges"))
            .collect();

        let mut regions: Vec<TopoRegion<Data>> = self.regions.into_iter().map(|build_region| {
            let BuildRegion { data, outer_rings, inner_rings } = build_region;

            let topo_outer_rings: Vec<TopoRing<Data>> = outer_rings.into_iter()
                .map(|r| build_ring_to_topo_ring_with_null_ptrs(&edges, &r)).collect();
            let topo_inner_rings: Vec<TopoRing<Data>> = inner_rings.into_iter()
                .map(|r| build_ring_to_topo_ring_with_null_ptrs(&edges, &r)).collect();

            TopoRegion {
                data: data,
                outer_rings: topo_outer_rings.into_boxed_slice(),
                inner_rings: topo_inner_rings.into_boxed_slice(),
            }
        }).collect();

        for mut region in regions.iter_mut() {
            let region_p = region as *const TopoRegion<Data>;

            for mut ring in region.outer_rings.iter_mut().chain(region.inner_rings.iter_mut()) {
                ring.region = region_p;

                for directed_edge in ring.directed_edges.iter() {
                    let mut edge = unsafe { &mut *(directed_edge.edge as *mut TopoEdge<Data>) };

                    let i = if edge.rings[0].is_null() {
                        0
                    } else {
                        assert!(edge.rings[1].is_null());
                        1
                    };

                    edge.rings[i] = ring as *const TopoRing<Data>;
                }
            }
        }

        Topology {
            regions: regions.into_boxed_slice(),
            edges: edges.into_boxed_slice(),
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
            topology.regions[0].outer_rings[0].directed_edges[1].edge,
            topology.regions[0].outer_rings[1].directed_edges[2].edge
        );
        assert_eq!(Direction::Backward, topology.regions[0].outer_rings[0].directed_edges[1].direction);
        assert_eq!(Direction::Forward, topology.regions[0].outer_rings[1].directed_edges[2].direction);
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
            topology.regions[0].outer_rings[0].directed_edges[1].edge,
            topology.regions[1].outer_rings[0].directed_edges[2].edge
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
        assert_eq!(1, topology.regions[0].outer_rings.len());
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
