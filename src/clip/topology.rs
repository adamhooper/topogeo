use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::mem;
use std::ptr;
use std::vec;

use geo::{Point, signed_area2};
use super::edge::clip_edge;
use super::types::ClipMask;
use topology::{Direction, DirectedEdge, TopoEdge, TopoRing, TopoRegion, Topology};

type EdgeId = usize;

#[derive(Debug)]
struct BuildRegion<Data> {
    data: Data,
    outer_rings: Box<[BuildRing]>,
    inner_rings: Box<[BuildRing]>,
}

#[derive(Debug)]
struct BuildRing(Box<[BuildDirectedEdge]>);

#[derive(Debug)]
struct BuildDirectedEdge {
    edge_id: EdgeId,
    direction: Direction,
}

fn first_point(points: &[Point], direction: Direction) -> Point {
    match direction {
        Direction::Forward => points[0],
        Direction::Backward => points[points.len() - 1],
    }
}

fn last_point(points: &[Point], direction: Direction) -> Point {
    match direction {
        Direction::Forward => points[points.len() - 1],
        Direction::Backward => points[0],
    }
}

#[derive(Debug,Eq,PartialEq,Hash,Clone,Copy)]
struct BuildEdge(Point, Point);

#[derive(Debug)]
struct NewEdgeSet {
    first_edge_id: EdgeId,
    edges: HashMap<BuildEdge, EdgeId>,
}

impl NewEdgeSet {
    fn new(first_edge_id: EdgeId) -> NewEdgeSet {
        NewEdgeSet {
            first_edge_id: first_edge_id,
            edges: HashMap::new(),
        }
    }

    fn len(&self) -> usize {
        self.edges.len()
    }

    fn build_directed_edge(&mut self, p1: &Point, p2: &Point) -> BuildDirectedEdge {
        let (a, b, dir) = if p1 < p2 { (p1, p2, Direction::Forward) } else { (p2, p1, Direction::Backward) };
        let edge = BuildEdge(*a, *b);
        let next_id: EdgeId = self.first_edge_id + self.edges.len();

        let edge_id = match self.edges.entry(edge) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                entry.insert(next_id);
                next_id
            }
        };

        BuildDirectedEdge { direction: dir, edge_id: edge_id }
    }

    /// Iterates over all edges, in ID order.
    fn into_iter(self) -> vec::IntoIter<BuildEdge> {
        let mut ret = vec![ BuildEdge(Point(0, 0), Point(0, 0)); self.len() ];
        for (build_edge, id) in self.edges.into_iter() {
            ret[id - self.first_edge_id] = build_edge;
        }
        ret.into_iter()
    }
}

fn build_ring_to_topo_ring_with_null_ptrs<Data>(edges: &[TopoEdge<Data>], build_ring: &BuildRing) -> TopoRing<Data> {
    let directed_edges: Vec<DirectedEdge<Data>> = build_ring.0.iter().map(|build_de| {
        DirectedEdge {
            edge: &edges[build_de.edge_id],
            direction: build_de.direction,
        }
    }).collect();

    TopoRing {
        directed_edges: directed_edges.into_boxed_slice(),
        region: ptr::null(),
    }
}

#[derive(Debug)]
struct Builder<Data> {
    regions: Vec<BuildRegion<Data>>,
    old_edge_0_ptr: *const TopoEdge<Data>,
    old_edges: Vec<Box<[Point]>>,
    old_edge_id_finder: Vec<Option<EdgeId>>,
    new_edges: NewEdgeSet,
}

impl<Data: Clone> Builder<Data> {
    fn new(topology: &Topology<Data>, mask: &ClipMask) -> Builder<Data> {
        // 1. Clip each edge individually. This will leave gaps sometimes; we'll
        // calculate those later.
        //
        // Also, forget about edge->ring->region pointers. Rebuild them later.
        let mut old_edge_id_finder: Vec<Option<EdgeId>> = Vec::with_capacity(topology.edges.len());
        let mut clipped_edges: Vec<Box<[Point]>> = Vec::with_capacity(topology.edges.len());

        for edge in topology.edges.iter() {
            // XXX we can flip an edge's direction here. That doesn't break
            // this module, but it might violate other modules' assumptions.
            let clipped = clip_edge(&edge.points[..], mask);
            if clipped.len() >= 2 {
                old_edge_id_finder.push(Some(clipped_edges.len() as EdgeId));
                clipped_edges.push(clipped);
            } else {
                old_edge_id_finder.push(None);
            }
        }

        let first_edge_id: EdgeId = clipped_edges.len();

        Builder {
            regions: Vec::with_capacity(topology.regions.len()),
            old_edge_0_ptr: topology.edges.as_ptr(),
            old_edges: clipped_edges,
            old_edge_id_finder: old_edge_id_finder,
            new_edges: NewEdgeSet::new(first_edge_id),
        }
    }

    fn add_region(&mut self, region: &TopoRegion<Data>) {
        let outer_rings = self.clip_rings(&region.outer_rings[..]);
        if outer_rings.len() > 0 {
            let inner_rings = self.clip_rings(&region.inner_rings[..]);

            self.regions.push(BuildRegion {
                data: region.data.clone(),
                outer_rings: outer_rings,
                inner_rings: inner_rings,
            });
        }
    }

    /// Returns a clipped version of the given Rings.
    ///
    /// May be an empty slice, if no rings remain.
    fn clip_rings(&mut self, rings: &[TopoRing<Data>]) -> Box<[BuildRing]> {
        let ret: Vec<BuildRing> = rings.iter().flat_map(|r| self.clip_ring(r)).collect();
        ret.into_boxed_slice()
    }

    /// Returns a clipped version of the given Ring.
    ///
    /// Returns None iff the new ring would have area 0.
    fn clip_ring(&mut self, ring: &TopoRing<Data>) -> Option<BuildRing> {
        let mut ret: Vec<BuildDirectedEdge> = Vec::with_capacity(2 * ring.directed_edges.len());

        let mut area2: i64 = 0;
        let mut start_point: Option<Point> = None;
        let mut previous_point: Option<Point> = None;

        for de in ring.directed_edges.iter() {
            match self.find_old_edge_id(de.edge) {
                Some(edge_id) => {
                    let ref old_edge = &(*self.old_edges[edge_id])[..];

                    if start_point.is_none() {
                        start_point = Some(first_point(old_edge, de.direction));
                    }

                    // If there's a gap between the last visible edge and
                    // this one, it's because the last edge left the clip area
                    // and the current edge is re-entering. Add a straight line
                    // between the exit and entry point.
                    if let Some(p) = previous_point {
                        let edge_start_point = first_point(old_edge, de.direction);
                        if p != edge_start_point {
                            area2 += signed_area2([ p, edge_start_point ].iter());
                            ret.push(self.new_edges.build_directed_edge(&p, &edge_start_point));
                        }
                    }

                    ret.push(BuildDirectedEdge { direction: de.direction, edge_id: edge_id });

                    previous_point = Some(last_point(old_edge, de.direction));

                    area2 += match de.direction {
                        Direction::Forward => signed_area2(old_edge.iter()),
                        Direction::Backward => signed_area2(old_edge.iter().rev()),
                    };
                }
                None => {
                    // This edge was entirely clipped: there's nothing left to add
                }
            };
        }

        // Plug a gap -- same rationale as above
        match (start_point, previous_point) {
            (Some(p0), Some(pn)) if p0 != pn => {
                ret.push(self.new_edges.build_directed_edge(&pn, &p0));
                area2 += signed_area2([ pn, p0 ].iter());
            }
            _ => {}
        }

        if area2 == 0 {
            // Clipped region has area 0
            None
        } else {
            Some(BuildRing(ret.into_boxed_slice()))
        }
    }

    fn find_old_edge_id(&self, old_edge_ptr: *const TopoEdge<Data>) -> Option<EdgeId> {
        let size = mem::size_of::<TopoEdge<Data>>();
        let offset_bytes = (old_edge_ptr as usize) - (self.old_edge_0_ptr as usize);
        let offset = offset_bytes / size;
        self.old_edge_id_finder[offset]
    }

    fn into_topology(self) -> Topology<Data> {
        // Build edges. Make all their ring pointers null.
        let mut edges: Vec<TopoEdge<Data>> = Vec::with_capacity(self.old_edges.len() + self.new_edges.len());
        edges.extend(self.old_edges.into_iter().map(|points| {
            TopoEdge {
                points: points,
                rings: [ ptr::null(), ptr::null() ],
            }
        }));
        edges.extend(self.new_edges.into_iter().map(|build_edge| {
            TopoEdge {
                points: Box::new([ build_edge.0, build_edge.1 ]),
                rings: [ ptr::null(), ptr::null() ],
            }
        }));

        // Build regions and their rings. Make all region pointers null.
        let mut regions: Vec<TopoRegion<Data>> = self.regions.into_iter().map(|build_region| {
            let BuildRegion { data, outer_rings, inner_rings } = build_region;
            let topo_outer_rings: Vec<TopoRing<Data>> = outer_rings.into_iter()
                .map(|r| build_ring_to_topo_ring_with_null_ptrs(&edges[..], &r)).collect();
            let topo_inner_rings: Vec<TopoRing<Data>> = inner_rings.into_iter()
                .map(|r| build_ring_to_topo_ring_with_null_ptrs(&edges[..], &r)).collect();

            TopoRegion {
                data: data,
                outer_rings: topo_outer_rings.into_boxed_slice(),
                inner_rings: topo_inner_rings.into_boxed_slice(),
            }
        }).collect();

        // Now that regions and edges have their final spots in memory, we can
        // set pointers to them.
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

pub fn clip_topology<Data: Clone>(topology: &Topology<Data>, mask: &ClipMask) -> Topology<Data> {
    let mut builder = Builder::new(&topology, mask);

    for region in topology.regions.iter() {
        builder.add_region(region);
    }

    builder.into_topology()
}

#[cfg(test)]
mod test {
    use std::ptr;
    use topology::{ Direction, DirectedEdge, TopoEdge, TopoRing, TopoRegion, Topology };
    use geo::Point;
    use clip::ClipMask;
    use super::clip_topology;

    // These test topologies use `ptr::null()` in place of real pointers,
    // because the clipping algorithm rewrites all pointers anyway.

    #[test]
    fn clip_island() {
        let edges = vec![
            TopoEdge::<()> {
                points: vec![ Point(1, 1), Point(10, 10), Point(10, 20), Point(1, 1) ].into_boxed_slice(),
                rings: [ ptr::null(), ptr::null() ],
            },
        ].into_boxed_slice();

        let topology = Topology {
            regions: vec![
                TopoRegion {
                    data: (),
                    outer_rings: vec![
                        TopoRing {
                            directed_edges: vec![
                                DirectedEdge { edge: &edges[0], direction: Direction::Forward }
                            ].into_boxed_slice(),
                            region: ptr::null(),
                        }
                    ].into_boxed_slice(),
                    inner_rings: vec![].into_boxed_slice(),
                },
            ].into_boxed_slice(),
            edges: edges,
        };

        let clipped = clip_topology(&topology, &ClipMask::MaxX(5));

        assert_eq!(
            vec![ Point(1, 1), Point(5, 5), Point(5, 10), Point(1, 1) ],
            clipped.edges[0].points.to_vec()
        );
        assert_eq!(&clipped.regions[0].outer_rings[0] as *const TopoRing<()>, clipped.edges[0].rings[0]);
        assert_eq!(&clipped.regions[0] as *const TopoRegion<()>, clipped.regions[0].outer_rings[0].region);
    }

    #[test]
    fn remove_region() {
        let edges = vec![
            TopoEdge::<u8> {
                points: vec![ Point(1, 1), Point(10, 10), Point(10, 20), Point(1, 1) ].into_boxed_slice(),
                rings: [ ptr::null(), ptr::null() ],
            },
            TopoEdge::<u8> {
                points: vec![ Point(100, 100), Point(101, 100), Point(100, 101), Point(100, 100) ].into_boxed_slice(),
                rings: [ ptr::null(), ptr::null() ],
            },
        ].into_boxed_slice();

        let topology = Topology {
            regions: vec![
                TopoRegion {
                    data: 0u8,
                    outer_rings: vec![
                        TopoRing {
                            directed_edges: vec![
                                DirectedEdge { edge: &edges[0], direction: Direction::Forward }
                            ].into_boxed_slice(),
                            region: ptr::null(),
                        }
                    ].into_boxed_slice(),
                    inner_rings: vec![].into_boxed_slice(),
                },
                TopoRegion {
                    data: 1u8,
                    outer_rings: vec![
                        TopoRing {
                            directed_edges: vec![
                                DirectedEdge { edge: &edges[1], direction: Direction::Forward }
                            ].into_boxed_slice(),
                            region: ptr::null(),
                        }
                    ].into_boxed_slice(),
                    inner_rings: vec![].into_boxed_slice(),
                },
            ].into_boxed_slice(),
            edges: edges,
        };

        let clipped = clip_topology(&topology, &ClipMask::MinX(30));

        assert_eq!(1, clipped.edges.len());
        assert_eq!(
            vec![ Point(100, 100), Point(101, 100), Point(100, 101), Point(100, 100) ],
            clipped.edges[0].points.to_vec()
        );
        assert_eq!(1u8, clipped.regions[0].data);
    }

    #[test]
    fn remove_empty_line() {
        let edges = vec![
            TopoEdge::<()> {
                points: vec![ Point(1, 1), Point(10, 10), Point(10, 20), Point(1, 1) ].into_boxed_slice(),
                rings: [ ptr::null(), ptr::null() ],
            },
        ].into_boxed_slice();

        let topology = Topology {
            regions: vec![
                TopoRegion {
                    data: (),
                    outer_rings: vec![
                        TopoRing {
                            directed_edges: vec![
                                DirectedEdge { edge: &edges[0], direction: Direction::Forward }
                            ].into_boxed_slice(),
                            region: ptr::null(),
                        }
                    ].into_boxed_slice(),
                    inner_rings: vec![].into_boxed_slice(),
                },
            ].into_boxed_slice(),
            edges: edges,
        };

        let clipped = clip_topology(&topology, &ClipMask::MinX(10));

        assert_eq!(0, clipped.regions.len());
    }
}
