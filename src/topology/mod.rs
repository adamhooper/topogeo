use std::cmp;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::hash::{Hash, Hasher};

use geo::{WindingOrder, Edge, Point, Ring, Region};

/// A graph of non-overlapping polygons.
///
/// The graph is made up of Nodes, Edges, Rings and Regions. Top-down: a
/// TopoRegion is composed of many TopoRings (some outer polygons, others holes,
/// depending on direction). Each TopoRing consists of one or more Edges. Each
/// TopoEdge has a start Node, and end Node, and some mid-Points.
///
/// The difference between a Node and a mid-Point is that Nodes _may_ represent
/// the vertex of three or more TopoRings -- that is, they're contained in three
/// or more Edges. We won't move them when we simplify().
pub struct Topology<Data> {
    pub regions: Box<[Box<TopoRegion<Data>>]>,
    pub edges: Box<[Box<TopoEdge<Data>>]>,
}

/// A group of TopoRings that _means_ something.
///
/// The "data" indicates what it means.
#[derive(Debug)]
pub struct TopoRegion<Data> {
    pub data: Data,
    pub outer_rings: Vec<Box<TopoRing<Data>>>,
    pub inner_rings: Vec<Box<TopoRing<Data>>>,
}

/// A polygon.
///
/// If edges go clockwise, the edges form the _outside_ boundary of a TopoRegion.
/// If edges go counter-clockwise, the edges form the _inside_ boundary (i.e.,
/// this is a "hole" in a polygon).
#[derive(Debug)]
pub struct TopoRing<Data> {
    pub directed_edges: Vec<DirectedEdge<Data>>,
    pub region: *const TopoRegion<Data>,
}

#[derive(Debug)]
pub struct DirectedEdge<Data> {
    pub edge: *const TopoEdge<Data>,
    pub direction: Direction,
}

#[derive(Debug,PartialEq,Eq)]
pub enum Direction {
    Forward,
    Backward
}

/// A direction-less path between two Nodes.
///
/// The path has no direction: there is only the canonical TopoEdge, which goes
/// from top-left Node to bottom-right Node. If you want a directed path, use
/// DirectedEdge.
///
/// A Topology can only contain a single TopoEdge with the given points.
#[derive(Clone, Debug)]
pub struct TopoEdge<Data> {
    pub points: Vec<Point>,
    pub rings: Vec<*const TopoRing<Data>>,
}

impl<Data> PartialOrd for TopoEdge<Data> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.points.partial_cmp(&other.points)
    }
}

impl<Data> Ord for TopoEdge<Data> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.points.cmp(&other.points)
    }
}

impl<Data> PartialEq for TopoEdge<Data> {
    fn eq(&self, other: &TopoEdge<Data>) -> bool {
        // condition: both Edges are in the same Topology
        self.points == other.points
    }
}
impl<Data> Eq for TopoEdge<Data> {}

impl<Data> Hash for TopoEdge<Data> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.points.hash(state);
    }
}

pub struct TopologyBuilder<Data> {
    regions: Vec<Box<TopoRegion<Data>>>,
    // HashMap's Entry API lets us insert-or-get the key
    edges: HashMap<Box<TopoEdge<Data>>,()>,
}

impl<Data> TopologyBuilder<Data>
    where Data: Clone
{
    pub fn new() -> TopologyBuilder<Data> {
        TopologyBuilder::<Data> {
            regions: vec!(),
            edges: HashMap::new(),
        }
    }

    pub fn add_region(&mut self, region: &Region<Data>) {
        assert!(region.outer_rings.len() > 0);

        let mut topo_region = Box::new(TopoRegion {
            data: region.data.clone(),
            outer_rings: Vec::with_capacity(region.outer_rings.len()),
            inner_rings: Vec::with_capacity(region.inner_rings.len()),
        });

        for ref input_ring in region.outer_rings.iter() {
            let ring = self.build_ring(&input_ring, &topo_region);
            topo_region.outer_rings.push(ring);
        }

        for ref input_ring in region.inner_rings.iter() {
            let ring = self.build_ring(&input_ring, &topo_region);
            topo_region.inner_rings.push(ring);
        }

        self.regions.push(topo_region);
    }

    /// Returns a Ring, building any Edges and Nodes that are missing.
    fn build_ring(&mut self, ring: &Ring, region: &TopoRegion<Data>) -> Box<TopoRing<Data>> {
        let edges = ring.edges();

        let mut ret = Box::new(TopoRing {
            region: region,
            directed_edges: Vec::with_capacity(edges.len()),
        });

        for ref edge in edges.iter() {
            let directed_edge = self.build_directed_edge(edge, &*ret);
            ret.directed_edges.push(directed_edge);
        }

        ret
    }

    fn build_directed_edge(&mut self, edge: &Edge, ring: *const TopoRing<Data>) -> DirectedEdge<Data> {
        let mut points = edge.0.clone();

        assert!(points.len() >= 2);

        let p1 = points[0];
        let p2 = points[points.len() - 1];

        let direction = if p1 < p2 || (p1 == p2 && Ring::Points(points.clone()).winding_order() == WindingOrder::Clockwise) {
            Direction::Forward
        } else {
            points.reverse();
            Direction::Backward
        };

        println!("Points: {:?}", points.to_vec());

        let mut maybe_new_edge = Box::new(TopoEdge { points: points.into_vec(), rings: vec![] });
        let maybe_new_edge_p: *mut TopoEdge<Data> = &mut *maybe_new_edge;

        let edge_p: *mut TopoEdge<Data> = match self.edges.entry(maybe_new_edge) {
            Entry::Occupied(entry) => {
                &**entry.key() as *const TopoEdge<Data> as *mut TopoEdge<Data>
            },
            Entry::Vacant(entry) => {
                entry.insert(());
                maybe_new_edge_p
            }
        };

        unsafe {
            (*edge_p).rings.push(ring);
        }

        DirectedEdge { edge: edge_p, direction: direction }
    }

    pub fn into_topology(self) -> Topology<Data> {
        // We'll sort() the edges, so that normalize() can _really_ normalize.
        let mut edges = Vec::<Box<TopoEdge<Data>>>::with_capacity(self.edges.len());
        for (edge, _) in self.edges {
            edges.push(edge);
        }
        edges.sort();
        Topology {
            regions: self.regions.into_boxed_slice(),
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

        builder.add_region(&Region::<u32> {
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
        builder.add_region(&Region::<()> {
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
        builder.add_region(&Region::<()> {
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

        builder.add_region(&Region::<()> {
            data: (),
            outer_rings: vec![ Ring::Points(vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ].into_boxed_slice()) ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice(),
        });

        builder.add_region(&Region::<()> {
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

        builder.add_region(&Region::<()> {
            data: (),
            outer_rings: vec![ Ring::Points(vec![ Point(0, 0), Point(3, 0), Point(0, 3), Point(0, 0) ].into_boxed_slice()) ].into_boxed_slice(),
            inner_rings: vec![ Ring::Points(vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ].into_boxed_slice()) ].into_boxed_slice(),
        });

        let topology = builder.into_topology();

        assert_eq!(6, topology.edges.len());
    }
}
