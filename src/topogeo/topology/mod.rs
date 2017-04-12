#[cfg(test)]
use std::collections::HashMap;
#[cfg(test)]
use std::collections::hash_map::Entry;
#[cfg(test)]
use std::hash::{Hash, Hasher};

/// A graph of non-overlapping polygons.
///
/// The graph is made up of Nodes, Edges, Rings and Regions. Top-down: a
/// Region is composed of many Rings (some outer polygons, others holes,
/// depending on direction). Each Ring consists of one or more Edges. Each
/// Edge has a start Node, and end Node, and some mid-Points.
///
/// The difference between a Node and a mid-Point is that Nodes _may_ represent
/// the vertex of three or more Rings -- that is, they're contained in three
/// or more Edges. We won't move them when we simplify().
#[cfg(test)]
pub struct Topology<Data> {
    regions: Vec<Box<Region<Data>>>,
    nodes: HashMap<Point,Box<Node<Data>>>,
    // HashMap's Entry API lets us insert-or-get the key
    edges: HashMap<Box<Edge<Data>>,()>,
}

/// A group of Rings that _means_ something.
///
/// The "data" indicates what it means.
#[derive(Debug)]
#[cfg(test)]
pub struct Region<Data> {
    data: Data,
    rings: Vec<Box<Ring<Data>>>,
}

/// A polygon.
///
/// If edges go clockwise, the edges form the _outside_ boundary of a Region.
/// If edges go counter-clockwise, the edges form the _inside_ boundary (i.e.,
/// this is a "hole" in a polygon).
#[derive(Debug)]
#[cfg(test)]
pub struct Ring<Data> {
    directed_edges: Vec<DirectedEdge<Data>>,
    region: *const Region<Data>,
}

#[derive(Debug)]
#[cfg(test)]
pub struct DirectedEdge<Data> {
    edge: *const Edge<Data>,
    direction: Direction,
}

#[derive(Debug,PartialEq,Eq)]
#[cfg(test)]
pub enum Direction {
    Forward,
    Backward
}

/// A direction-less path between two Nodes.
///
/// The path has no direction: there is only the canonical Edge, which goes
/// from top-left Node to bottom-right Node. If you want a directed path, use
/// DirectedEdge.
#[derive(Clone, Debug)]
#[cfg(test)]
pub struct Edge<Data> {
    node1: *const Node<Data>,
    node2: *const Node<Data>,
    mid_points: Vec<Point>,
    rings: Vec<*const Ring<Data>>,
}

/// A node in the Topology graph.
///
/// Each Node forms the beginning and/or end of one or more Edges. (A circular
/// Edge has the same Node as its start ane end.)
#[derive(Debug, Eq)]
#[cfg(test)]
pub struct Node<Data> {
    point: Point,
    edges: Vec<*const Edge<Data>>,
}

/// A place in space.
///
/// Maybe this should be a generic type. For us, it's a [longitude,latitude]
/// pair, scaled up so longitude is from 0 (180°W) to 2^32-1 (180°E) and
/// latitude is from 0 (90°N) to 2^31-1 (90°S).
///
/// Point is comparable so Edge can have a canonical direction (top-left to
/// bottom-right, conceptually). That helps us build EdgeSet without checking
/// two directions.
#[derive(Clone, Copy, Debug, Hash, Ord, Eq, PartialEq, PartialOrd)]
#[cfg(test)]
pub struct Point(u32, u32);

#[cfg(test)]
impl<Data> PartialEq for Edge<Data> {
    fn eq(&self, other: &Edge<Data>) -> bool {
        // conditions:
        // * both Edges are in the same Topology
        // * there's only one Node per unique Point in a Topology
        self.node1 == other.node1 && self.node2 == other.node2 && self.mid_points == other.mid_points
    }
}
#[cfg(test)]
impl<Data> Eq for Edge<Data> {}

#[cfg(test)]
impl<Data> Hash for Edge<Data> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.node1.hash(state);
        self.node2.hash(state);
        self.mid_points.hash(state);
    }
}

#[cfg(test)]
impl<Data> PartialEq for Node<Data> {
    fn eq(&self, other: &Node<Data>) -> bool {
        // conditions:
        // * there's only one Node per unique Point on a Topology
        // * we never compare across two Topologies (or if we do, we want two
        //   Nodes to be Equal iff their Points are equal)
        self.point == other.point
    }
}

#[cfg(test)]
impl<Data> Hash for Node<Data> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.point.hash(state)
    }
}

#[cfg(test)]
pub struct TopologyBuilder<Data> {
    topology: Topology<Data>,
}

#[cfg(test)]
impl<Data> TopologyBuilder<Data> {
    pub fn new() -> TopologyBuilder<Data> {
        TopologyBuilder::<Data> {
            topology: Topology {
                regions: vec!(),
                nodes: HashMap::new(),
                edges: HashMap::new(),
            }
        }
    }

    pub fn add_region(&mut self, data: Data, points: &[&[Point]]) {
        let mut region = Box::new(Region { data: data, rings: Vec::with_capacity(points.len()) });

        for &edge_points in points {
            let ring = self.build_ring(&edge_points, &region);
            region.rings.push(ring);
        }

        self.topology.regions.push(region);
    }

    /// Returns a Ring, building any Edges and Nodes that are missing.
    fn build_ring(&mut self, points: &[Point], region: &Region<Data>) -> Box<Ring<Data>> {
        assert!(points.len() > 2);

        let mut ring = Box::new(Ring {
            directed_edges: Vec::with_capacity(points.len() - 1),
            region: region,
        });

        for two_points in points.windows(2) {
            let directed_edge = self.build_directed_edge(two_points[0], two_points[1], &*ring);
            ring.directed_edges.push(directed_edge);
        }

        ring
    }

    fn build_directed_edge(&mut self, p1: Point, p2: Point, ring: *const Ring<Data>) -> DirectedEdge<Data> {
        let n1: *mut Node<Data> = self.maybe_build_node(p1);
        let n2: *mut Node<Data> = self.maybe_build_node(p2);

        let (a, b, direction) = if p1 <= p2 {
            (n1, n2, Direction::Forward)
        } else {
            (n2, n1, Direction::Backward)
        };

        let mut maybe_new_edge = Box::new(Edge { node1: a, node2: b, mid_points: vec![], rings: vec![] });
        let maybe_new_edge_p: *mut Edge<Data> = &mut *maybe_new_edge;

        let edge_p: *mut Edge<Data> = match self.topology.edges.entry(maybe_new_edge) {
            Entry::Occupied(entry) => { &**entry.key() as *const Edge<Data> as *mut Edge<Data> }
            Entry::Vacant(entry) => {
                entry.insert(());
                maybe_new_edge_p
            }
        };

        unsafe {
            (*edge_p).rings.push(ring);
            let edge_p_const: *const Edge<Data> = edge_p;

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

        builder.add_region(42, &[
           &[ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ],
           &[ Point(10, 10), Point(20, 10), Point(10, 20), Point(10, 10) ],
        ]);

        let topology = builder.into_topology();

        assert_eq!(1, topology.regions.len());
        assert_eq!(6, topology.edges.len());
        assert_eq!(6, topology.nodes.len());
    }

    #[test]
    fn share_point() {
        let mut builder = TopologyBuilder::<()>::new();

        // *--*--*
        // | / \ |
        // |/   \|
        // *     *
        builder.add_region((), &[
           &[ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ],
           &[ Point(2, 1), Point(3, 1), Point(3, 2), Point(2, 1) ],
        ]);

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
        builder.add_region((), &[
           &[ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ],
           &[ Point(2, 1), Point(2, 2), Point(1, 2), Point(2, 1) ],
        ]);

        let topology = builder.into_topology();

        assert_eq!(1, topology.regions.len());
        assert_eq!(5, topology.edges.len());
        assert_eq!(4, topology.nodes.len());
        assert_eq!(Some(3), topology.nodes.get(&Point(2, 1)).map(|n| n.edges.len()));

        assert_eq!(
            topology.regions[0].rings[0].directed_edges[1].edge,
            topology.regions[0].rings[1].directed_edges[2].edge
        );
        assert_eq!(Direction::Backward, topology.regions[0].rings[0].directed_edges[1].direction);
        assert_eq!(Direction::Forward, topology.regions[0].rings[1].directed_edges[2].direction);
    }

    #[test]
    fn share_edge_two_regions() {
        let mut builder = TopologyBuilder::<()>::new();

        builder.add_region((), &[&[ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ] ]);
        builder.add_region((), &[&[ Point(2, 1), Point(2, 2), Point(1, 2), Point(2, 1) ] ]);

        let topology = builder.into_topology();

        assert_eq!(5, topology.edges.len());
        assert_eq!(
            topology.regions[0].rings[0].directed_edges[1].edge,
            topology.regions[1].rings[0].directed_edges[2].edge
        );
    }
}
