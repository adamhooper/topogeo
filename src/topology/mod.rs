mod types;
mod build;

pub use self::types::{Topology, TopoEdge, TopoRegion, TopoRing, DirectedEdge, Direction, TopoRingId, TopoEdgeId, TopoRegionId, NULL_ID};
pub use self::build::TopologyBuilder;
