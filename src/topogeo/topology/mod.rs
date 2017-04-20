use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::hash::{Hash, Hasher};

use topogeo::Point;
use topogeo::geo::{WindingOrder, Edge, Ring, Region};

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
    pub regions: Vec<Box<TopoRegion<Data>>>,
    pub nodes: HashMap<Point,Box<Node<Data>>>,
    // HashMap's Entry API lets us insert-or-get the key
    pub edges: HashMap<Box<TopoEdge<Data>>,()>,
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
#[derive(Clone, Debug)]
pub struct TopoEdge<Data> {
    pub node1: *const Node<Data>,
    pub node2: *const Node<Data>,
    pub mid_points: Vec<Point>,
    pub rings: Vec<*const TopoRing<Data>>,
}

/// A node in the Topology graph.
///
/// Each Node forms the beginning and/or end of one or more Edges. (A circular
/// TopoEdge has the same Node as its start ane end.)
#[derive(Debug, Eq)]
pub struct Node<Data> {
    pub point: Point,
    pub edges: Vec<*const TopoEdge<Data>>,
}

impl<Data> PartialEq for TopoEdge<Data> {
    fn eq(&self, other: &TopoEdge<Data>) -> bool {
        // conditions:
        // * both Edges are in the same Topology
        // * there's only one Node per unique Point in a Topology
        self.node1 == other.node1 && self.node2 == other.node2 && self.mid_points == other.mid_points
    }
}
impl<Data> Eq for TopoEdge<Data> {}

impl<Data> Hash for TopoEdge<Data> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.node1.hash(state);
        self.node2.hash(state);
        self.mid_points.hash(state);
    }
}

impl<Data> PartialEq for Node<Data> {
    fn eq(&self, other: &Node<Data>) -> bool {
        // conditions:
        // * there's only one Node per unique Point on a Topology
        // * we never compare across two Topologies (or if we do, we want two
        //   Nodes to be Equal iff their Points are equal)
        self.point == other.point
    }
}

impl<Data> Hash for Node<Data> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.point.hash(state)
    }
}

pub struct TopologyBuilder<Data> {
    topology: Topology<Data>,
}

impl<Data> TopologyBuilder<Data>
    where Data: Clone
{
    pub fn new() -> TopologyBuilder<Data> {
        TopologyBuilder::<Data> {
            topology: Topology {
                regions: vec!(),
                nodes: HashMap::new(),
                edges: HashMap::new(),
            }
        }
    }

    pub fn add_region(&mut self, region: &Region<Data>) {
        assert!(region.outer_rings.len() > 0);

        let mut topo_region = Box::new(TopoRegion {
            data: region.data.clone(),
            outer_rings: Vec::with_capacity(region.outer_rings.len()),
            inner_rings: Vec::with_capacity(region.inner_rings.len()),
        });

        for ref input_ring in &region.outer_rings {
            let ring = self.build_ring(&input_ring, &topo_region);
            topo_region.outer_rings.push(ring);
        }

        for ref input_ring in &region.inner_rings {
            let ring = self.build_ring(&input_ring, &topo_region);
            topo_region.inner_rings.push(ring);
        }

        self.topology.regions.push(topo_region);
    }

    /// Returns a Ring, building any Edges and Nodes that are missing.
    fn build_ring(&mut self, ring: &Ring, region: &TopoRegion<Data>) -> Box<TopoRing<Data>> {
        let edges = ring.edges();

        let mut ret = Box::new(TopoRing {
            region: region,
            directed_edges: Vec::with_capacity(edges.len()),
        });

        for ref edge in edges {
            let directed_edge = self.build_directed_edge(edge, &*ret);
            ret.directed_edges.push(directed_edge);
        }

        ret
    }

    fn build_directed_edge(&mut self, edge: &Edge, ring: *const TopoRing<Data>) -> DirectedEdge<Data> {
        let ref points = edge.0;

        assert!(points.len() >= 2);

        let p1 = points[0];
        let p2 = points[points.len() - 1];
        let n1: *mut Node<Data> = self.maybe_build_node(p1);
        let n2: *mut Node<Data> = self.maybe_build_node(p2);
        let mut mid = points[1 .. points.len() - 1].to_vec(); // may be reverse()d

        let (a, b, direction) = if p1 < p2 || p1 == p2 && Ring::Points(points.clone()).winding_order() == WindingOrder::Clockwise {
            (n1, n2, Direction::Forward)
        } else {
            mid.reverse();
            (n2, n1, Direction::Backward)
        };

        let mut maybe_new_edge = Box::new(TopoEdge { node1: a, node2: b, mid_points: mid, rings: vec![] });
        let maybe_new_edge_p: *mut TopoEdge<Data> = &mut *maybe_new_edge;

        let edge_p: *mut TopoEdge<Data> = match self.topology.edges.entry(maybe_new_edge) {
            Entry::Occupied(entry) => { &**entry.key() as *const TopoEdge<Data> as *mut TopoEdge<Data> }
            Entry::Vacant(entry) => {
                entry.insert(());
                maybe_new_edge_p
            }
        };

        unsafe {
            (*edge_p).rings.push(ring);
            let edge_p_const: *const TopoEdge<Data> = edge_p;

            // O(n) contains() call should be quick in practice since most
            // nodes have few edges
            if !(*a).edges.contains(&edge_p_const) {
                (*a).edges.push(edge_p);
                (*b).edges.push(edge_p);
            }
        }

        DirectedEdge { edge: edge_p, direction: direction }
    }

    fn maybe_build_node(&mut self, point: Point) -> *mut Node<Data> {
        let mut node: &mut Box<Node<Data>> = self.topology.nodes
            .entry(point)
            .or_insert(Box::new(Node { point: point, edges: vec![] }));

        &mut **node
    }

    pub fn into_topology(self) -> Topology<Data> {
        self.topology
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
                Ring::Points(vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ]),
                Ring::Points(vec![ Point(10, 10), Point(20, 10), Point(10, 20), Point(10, 10) ]),
            ],
            inner_rings: vec![],
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
                Ring::Points(vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ]),
                Ring::Points(vec![ Point(2, 1), Point(3, 1), Point(3, 2), Point(2, 1) ]),
            ],
            inner_rings: vec![]
        });

        let topology = builder.into_topology();

        assert_eq!(1, topology.regions.len());
        assert_eq!(6, topology.edges.len());
        assert_eq!(5, topology.nodes.len());
        assert_eq!(Some(4), topology.nodes.get(&Point(2, 1)).map(|n| n.edges.len()));
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
                Ring::Points(vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ]),
                Ring::Points(vec![ Point(2, 1), Point(2, 2), Point(1, 2), Point(2, 1) ]),
            ],
            inner_rings: vec![
            ]
        });

        let topology = builder.into_topology();

        assert_eq!(1, topology.regions.len());
        assert_eq!(5, topology.edges.len());
        assert_eq!(Some(3), topology.nodes.get(&Point(2, 1)).map(|n| n.edges.len()));

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
            outer_rings: vec![ Ring::Points(vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ]) ],
            inner_rings: vec![],
        });

        builder.add_region(&Region::<()> {
            data: (),
            outer_rings: vec![ Ring::Points(vec![ Point(2, 1), Point(2, 2), Point(1, 2), Point(2, 1) ]) ],
            inner_rings: vec![],
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
            outer_rings: vec![ Ring::Points(vec![ Point(0, 0), Point(3, 0), Point(0, 3), Point(0, 0) ]) ],
            inner_rings: vec![ Ring::Points(vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ]) ],
        });

        let topology = builder.into_topology();

        assert_eq!(6, topology.edges.len());
    }
}
