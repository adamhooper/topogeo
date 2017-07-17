use geo::Point;

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
    pub regions: Box<[TopoRegion<Data>]>,
    pub rings: Box<[TopoRing]>,
    pub edges: Box<[TopoEdge]>,
}

// There are a few ways to represent a graph:
//
// * Arc references: easy to get wrong, leading to leaks.
// * Pointers: needs unsafe{}; forces us to add Data type to Edges and Rings;
//             tricky to rewrite when, say, filtering or normalizing.
// * Array indexes: easier to understand than pointers, and take less space;
//                  means we need to store Rings in Topology structure
//                  directly (so we can point to it).
//
// After flirting with pointers, the final decision was array indexes.
pub type TopoRegionId = u32;
pub type TopoRingId = u32;
pub type TopoEdgeId = u32;
pub const NULL_ID: u32 = 0xffff as u32;

/// A group of TopoRings that _means_ something.
///
/// The "data" indicates what it means.
#[derive(Debug)]
pub struct TopoRegion<Data> {
    pub data: Data,
    pub outer_ring_ids: Box<[TopoRingId]>,
    pub inner_ring_ids: Box<[TopoRingId]>,
}

/// A polygon.
///
/// If edges go clockwise, the edges form the _outside_ boundary of a TopoRegion.
/// If edges go counter-clockwise, the edges form the _inside_ boundary (i.e.,
/// this is a "hole" in a polygon).
#[derive(Debug)]
pub struct TopoRing {
    pub directed_edges: Box<[DirectedEdge]>,
    pub region_id: TopoRegionId,
}

#[derive(Debug)]
pub struct DirectedEdge {
    pub edge_id: TopoEdgeId,
    pub direction: Direction,
}

#[derive(Debug,Clone,Copy,PartialEq,Eq)]
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
#[derive(Debug)]
pub struct TopoEdge {
    pub points: Box<[Point]>,
    pub ring1_id: TopoRingId,
    pub ring2_id: TopoRingId,
}
