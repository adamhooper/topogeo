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
    pub edges: Box<[TopoEdge<Data>]>,
}

/// A group of TopoRings that _means_ something.
///
/// The "data" indicates what it means.
#[derive(Debug)]
pub struct TopoRegion<Data> {
    pub data: Data,
    pub outer_rings: Box<[TopoRing<Data>]>,
    pub inner_rings: Box<[TopoRing<Data>]>,
}

/// A polygon.
///
/// If edges go clockwise, the edges form the _outside_ boundary of a TopoRegion.
/// If edges go counter-clockwise, the edges form the _inside_ boundary (i.e.,
/// this is a "hole" in a polygon).
#[derive(Debug)]
pub struct TopoRing<Data> {
    pub directed_edges: Box<[DirectedEdge<Data>]>,
    pub region: *const TopoRegion<Data>,
}

#[derive(Debug)]
pub struct DirectedEdge<Data> {
    pub edge: *const TopoEdge<Data>,
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
pub struct TopoEdge<Data> {
    pub points: Box<[Point]>,
    pub rings: [ *const TopoRing<Data>; 2 ],
}
