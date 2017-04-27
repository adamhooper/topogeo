use std::cmp::Ordering;
use std::collections::btree_map::{BTreeMap,Entry};
use itertools::Itertools;

use geo::{ Edge, Point, Ring, Region, WindingOrder };
use topology::{DirectedEdge, Direction, TopoEdge, TopoRegion, TopoRing, Topology, TopologyBuilder};

/// Ring data structure used when normalizing.
#[derive(Debug)]
struct NormRing<T> {
    edges: Vec<NormEdge<T>>,
}

impl<T> PartialOrd for NormRing<T> {
    fn partial_cmp(&self, other: &NormRing<T>) -> Option<Ordering> {
        Some(self.edges[0].points[0].cmp(&other.edges[0].points[0]))
    }
}

impl<T> Ord for NormRing<T> {
    fn cmp(&self, other: &NormRing<T>) -> Ordering {
        self.edges[0].points[0].cmp(&other.edges[0].points[0])
    }
}

impl<T> PartialEq for NormRing<T> {
    fn eq(&self, other: &NormRing<T>) -> bool {
        self.edges == other.edges
    }
}

impl<T> Eq for NormRing<T> {}

impl<T> NormRing<T> {
    fn into_ring(self) -> Ring {
        let edges: Vec<Edge> = self.edges.into_iter().map(|e| e.into_edge()).collect();
        Ring::Edges(edges.into_boxed_slice())
    }
}

/// Edge data structure used when normalizing.
#[derive(Debug,Eq)]
struct NormEdge<T> {
    points: Vec<Point>,
    regions: Vec<*const TopoRegion<T>>,
}

impl<T> PartialEq for NormEdge<T> {
    fn eq(&self, other: &NormEdge<T>) -> bool {
        self.points == other.points
    }
}

impl<T> NormEdge<T> {
    fn with_directed_edge(directed_edge: &DirectedEdge<T>) -> NormEdge<T> {
        let ref edge: &TopoEdge<_> = unsafe { &(*directed_edge.edge) };

        let mut points = edge.points.clone();
        if directed_edge.direction == Direction::Backward {
            points.reverse();
        }

        let regions: Vec<*const TopoRegion<T>> = edge.rings.iter().map(|&r| unsafe { (*r).region }).collect();
        assert!(regions.len() <= 2);

        NormEdge { points: points, regions: regions }
    }

    /// `true` iff this NormEdge is between two Rings in the same Region.
    fn is_redundant(&self) -> bool {
        self.regions.len() == 2 && self.regions[0] == self.regions[1]
    }

    fn into_edge(self) -> Edge {
        Edge(self.points.into_boxed_slice())
    }
}

impl<T> Clone for NormEdge<T> {
    fn clone(&self) -> NormEdge<T> {
        NormEdge {
            points: self.points.clone(),
            regions: self.regions.clone()
        }
    }
}

/// Returns an equivalent "island" edge (i.e., ring) whose first point is the
/// leftmost/topmost of the input points.
fn rotate_island_edge<T>(edge: &NormEdge<T>) -> NormEdge<T> {
    match edge.points.iter().enumerate().min_by_key(|&(_, p)| p) {
        None | Some((0, _)) => { NormEdge { points: edge.points.clone(), regions: edge.regions.clone() } },
        Some((index, _)) => {
            assert!(edge.points[0] == edge.points[edge.points.len() - 1]);

            let mut points = Vec::<Point>::with_capacity(edge.points.len());

            // The _old_ first and last points are identical, so we only want
            // one of them. The _new_ first and last points must be identical,
            // too, so we'll use two copies. That's what the `- 1` and `+ 1` are
            // about.
            points.extend_from_slice(&edge.points[index .. edge.points.len() - 1]);
            points.extend_from_slice(&edge.points[0 .. index + 1]);

            NormEdge { points: points, regions: edge.regions.clone() }
        }
    }
}

/// Returns an equivalend set of Edges, rotated so that the first Edge starts
/// at the leftmost/topmost Node.
fn rotate_edges<T>(edges: &Vec<NormEdge<T>>) -> Vec<NormEdge<T>> {
    if edges.len() == 1 {
        vec![ rotate_island_edge(&edges[0]) ]
    } else {
        match edges.iter().enumerate().min_by_key(|&(_, e)| e.points[0]) {
            None | Some((0, _)) => { edges.clone() }
            Some((index, _)) => {
                let mut ret = Vec::<NormEdge<T>>::with_capacity(edges.len());
                ret.extend_from_slice(&edges[ index .. ]);
                ret.extend_from_slice(&edges[ .. index ]);
                ret
            }
        }
    }
}

/// Returns an equivalent Vec of `NormEdge`s that has the smallest number of
/// elements possible.
///
/// Logic: when two consecutive `NormEdge`s share the same Rings, they are
/// merged into a single `NormEdge` with all the constituent points. ASCII
/// art:
///
/// ```ascii
/// *-------*
/// | a     |
/// A---B---C
/// | b     |
/// E-------D
/// ```
///
/// The input edges `AB` and `BC` are consecutive and they both bisect Regions
/// `a` and `b`. They will be joined into a single `NormEdge`, `ABC`.
///
/// The other edge, which separates `b` from nothing, will be joined into
/// `CDEA`.
///
/// The returned edges preserve input order (i.e., clockwise/counter-clockwise),
/// but they may be rotated. In this example, given edges
/// `[ AB, BC, CD, DE, EA ]` arbitrarily rotated,  the return values will be
/// either `[ ABC, CDEA ]` or `[ CDEA, ABC ]`.
///
/// Implementation note: we often call this function twice with the same Edge:
/// once for `a`'s `Ring` and once for `b`'s. Both calls will join `ABC` in the
/// same way (except at a Node joining two rings from the same Region to
/// a second Region ... which we fix in join_adjacent_rings()).
fn join_related_edges<T>(edges: &Vec<NormEdge<T>>) -> Vec<NormEdge<T>> {
    let mut ret = Vec::<NormEdge<T>>::new();

    for ref edge in edges {
        // Either extend the existing edge or add a new one
        let extended = match ret.last_mut() {
            Some(ref mut last) if last.regions == edge.regions => {
                last.points.extend_from_slice(&edge.points[1..]);
                true
            },
            _ => { false }
        };

        if !extended {
            ret.push((*edge).clone());
        }
    }

    if ret.len() > 1 {
        if ret[0].regions == ret.last().unwrap().regions {
            let mut points = ret.last().unwrap().points.clone();
            points.extend_from_slice(&ret[0].points[1..]);
            ret[0].points = points;
            ret.pop();
        }
    }

    ret
}

fn calculate_winding_order_from_edges<T>(edges: &Vec<NormEdge<T>>) -> WindingOrder {
    // https://en.wikipedia.org/wiki/Shoelace_formula
    let mut a: i64 = 0;

    for ref edge in edges {
        for (p1, p2) in edge.points.iter().tuple_windows() {
            a += (p1.0 as i64) * (p2.1 as i64) - (p2.0 as i64) * (p1.1 as i64)
        }
    }

    assert!(a != 0);
    if a > 0 {
        WindingOrder::Clockwise
    } else {
        WindingOrder::CounterClockwise
    }
}

/// If the given `NormEdge`s form a clockwise ring, return a copy; otherwise,
/// return a backwards copy.
fn wind_edges<T>(edges: &Vec<NormEdge<T>>, order: WindingOrder) -> Vec<NormEdge<T>> {
    if order == calculate_winding_order_from_edges(edges) {
        edges.clone()
    } else {
        let mut ret: Vec<NormEdge<T>> = Vec::with_capacity(edges.len());
        for ref edge in edges {
            let mut new_edge: NormEdge<T> = (*edge).clone();
            new_edge.points.reverse();
            ret.push(new_edge);
        }
        ret.reverse();
        ret
    }
}

/// Returns an equivalent Vec of `NormRing`s that has the smallest number of
/// elements possible.
///
/// Rationale: if any `NormEdge` `is_redundant()`, it can be removed to join two
/// `NormRing`s together. ASCII art:
///
/// ```ascii
/// A-------B
/// |       |
/// F-------C
/// |       |
/// E-------D
/// ```
///
/// Here, `FC` is a redundant edge.
///
/// Logic: glob all edges (from all rings) into a single BTreeSet, omitting
/// redundant edges. Remove the first edge from the set and "follow" it to form
/// the first Ring. Repeat until the set is empty.
///
/// This is O(N lg N); to speed things up, we pass through rings that aren't
/// redundant and we nix rings that are entirely redundant. (Exercise for the
/// reader: implement a faster algorithm.)
///
/// A bit more on these entirely-redundant "donuts":
///
/// ```ascii
/// A------B
/// |      |
/// | E--F |
/// | |  | |
/// | H--G |
/// |      |
/// D------C
/// ```
///
/// Imagine, in this diagram, `ABCD` has the "hole" `EHGF`, and `EFGH` is also a
/// ring representing the same region. Since `EFGH` (the area) is entirely
/// redundant, we'll nix it. Be sure to nix `EHGF` (the hole) as well!
///
/// Each input ring must be normalized; all output rings will be normalized as
/// well.
///
/// Input Rings may be in any order; output Rings will be in undefined order.
fn join_adjacent_rings<T>(rings: &Vec<NormRing<T>>) -> Vec<NormRing<T>> {
    let mut ret = Vec::<NormRing<T>>::with_capacity(rings.len()); // upper-bound capacity

    // NormRings are directed. We'll index them by their first Point. There's
    // no way for two non-redundant edges to leave the same Point.
    let mut to_merge: BTreeMap<Point, NormEdge<T>> = BTreeMap::new();

    for ref ring in rings {
        let (redundant, useful): (Vec<_>, Vec<_>) = ring.edges.clone().into_iter().partition(|ref e| e.is_redundant());

        match (redundant.len(), useful.len()) {
            (0, _) => {
                // entire ring has no redundant edges: pass it through
                ret.push(NormRing { edges: useful });
            }
            (_, 0) => {
                // ignore: the entire ring is redundant
            }
            _ => {
                // index the useful edges and ignore the redundant ones
                for ref edge in useful {
                    match to_merge.entry(edge.points[0]) {
                        Entry::Vacant(e) => {
                            e.insert(edge.clone());
                        }
                        Entry::Occupied(e) => {
                            panic!("Bug/edge case: two distinct edges in the same region are both trying to leave {:?}", e.key());
                        }
                    }
                }
            }
        }
    }

    if to_merge.len() == 0 {
        // No merging necessary! All rings are normalized and in order.
        return ret
    }

    // Now to reconstruct the rings we need to merge....
    while to_merge.len() > 0 {
        let start = *to_merge.keys().next().unwrap();
        let mut end = start;

        let mut edges: Vec<NormEdge<T>> = Vec::new();

        loop {
            match to_merge.remove(&end) {
                None => {
                    panic!("Expected Edge to continue past {:?} when building Ring", end);
                }
                Some(edge) => {
                    end = *edge.points.last().unwrap();
                    edges.push(edge);
                }
            }

            if end == start {
                // we've reconstructed a ring. to_merge may or may not be empty.
                break;
            }
        }

        edges = join_related_edges(&edges);
        edges = rotate_edges(&edges);

        ret.push(NormRing { edges: edges });
    }

    ret.sort();
    ret
}

/// Returns a normalized copy of the given set of outer/inner rings.
///
/// Call with WindingOrder::Clockwise on outer rings and CounterClockwise on
/// inner rings.
///
/// Note the tidy cleanup of donuts, even though this function isn't called
/// with both outer rings and inner rings at the same time (it either gets
/// all outer rings or all inner rings). For instance:
///
/// ```ascii
/// A------B
/// |      |
/// | E--H |
/// | |  | |
/// | F--G |
/// |      |
/// D------C
/// ```
///
/// If a region has two outer rings `ABCD` and `EHGF`, and one inner ring
/// ("hole"), `EFGH`, then this function's call to join_adjacent_rings() will
/// nix `EHGF` when called on outer rings, and it will nix `EFGH` when called
/// on inner rings (since the edges have two rings and thus two Regions, and
/// both Regions are identical). Ta-da! The donut is gone.
fn normalize_region_rings<T>(in_rings: &[Box<TopoRing<T>>], winding_order: WindingOrder) -> Box<[Ring]> {
    let mut rings = Vec::<NormRing<T>>::with_capacity(in_rings.len());

    for ref boxed_ring in in_rings {
        let ref in_ring = *boxed_ring;

        let mut edges = Vec::<NormEdge<T>>::with_capacity(in_ring.directed_edges.len());

        for ref directed_edge in &in_ring.directed_edges {
            edges.push(NormEdge::<T>::with_directed_edge(directed_edge));
        }

        edges = join_related_edges(&edges);
        edges = wind_edges(&edges, winding_order);
        edges = rotate_edges(&edges);

        rings.push(NormRing::<T> { edges: edges });
    }

    rings = join_adjacent_rings(&rings);
    rings.sort();

    let ret: Vec<Ring> = rings.into_iter().map(|r| r.into_ring()).collect();
    ret.into_boxed_slice()
}

/// Returns a "normalized" copy of the given Topology.
///
/// Normalization rules:
///
/// * **Fewest Rings possible**: A `Region` may not have two `Ring`s that share an `Edge`.
///   In other words: adjacent polygons must be merged.
/// * **Fewest Nodes and Edges possible**: No adjacent Edges may share the same Regions. In
///   other words: while all equivalent `Topology`s share the same `Point`s, a
///   *normalized* `Topology` has the most `mid_points` and the fewest `Node`s. An island
///   consists of a single *Edge*.
/// * **Ring direction**: Outer rings are clockwise; inner rings are counter-clockwise.
/// * **Left/Top-most ordering**: the first Edge in each Ring starts with the leftmost
///   (or in case of a tie, topmost) `Node`. The first Ring in each Region starts with
///   the leftmost or topmost `Node`.
/// * **Island Node**: An island (or lake) has one Node, and that's the leftmost (or
///   in case of a tie, topmost) `Point`.
pub fn normalize<Data: Copy>(topo: &Topology<Data>) -> Topology<Data> {
    let mut builder = TopologyBuilder::<Data>::new();

    for ref region in topo.regions.iter() {
        let outer_rings = normalize_region_rings(&region.outer_rings, WindingOrder::Clockwise);
        let inner_rings = normalize_region_rings(&region.inner_rings, WindingOrder::CounterClockwise);
        builder.add_region(&Region {
            data: region.data,
            outer_rings: outer_rings,
            inner_rings: inner_rings,
        });
    }

    builder.into_topology()
}

#[cfg(test)]
mod test {
    use geo::{Point, Region, Ring};
    use topology::{Direction, TopoEdge, TopoRing, TopologyBuilder};
    use normalize::normalize;

    fn edge_to_points<T>(edge: &TopoEdge<T>) -> Vec<Point> {
        edge.points.to_vec()
    }

    #[test]
    fn flatten_island() {
        let mut builder = TopologyBuilder::<()>::new();

        // A--B
        // | /
        // |/
        // C
        builder.add_region(&Region {
            data: (),
            outer_rings: vec![ Ring::Points(vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ].into_boxed_slice()) ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice(),
        });

        let topology = builder.into_topology();
        let normal = normalize(&topology);

        assert_eq!(1, normal.edges.len());
        let edge: &TopoEdge<_> = &*normal.edges[0];
        assert_eq!(vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ], edge_to_points(&edge));
    }

    #[test]
    fn flatten_uncommon_edges() {
        let mut builder = TopologyBuilder::<u32>::new();

        // *--*
        // | /|
        // |/ |
        // *--*
        builder.add_region(&Region {
            data: 1,
            outer_rings: vec![ Ring::Points(vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ].into_boxed_slice()) ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice(),
        });
        builder.add_region(&Region {
            data: 2,
            outer_rings: vec![ Ring::Points(vec![ Point(2, 1), Point(2, 2), Point(1, 2), Point(2, 1) ].into_boxed_slice()) ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice(),
        });

        let topology = builder.into_topology();
        let normal = normalize(&topology);

        assert_eq!(3, normal.edges.len());
        let edges: Vec<&TopoEdge<_>> = normal.edges.iter().map(|e| &**e).collect();
        let edge1 = edges.iter().find(|e| e.rings == vec![ &(*normal.regions[0].outer_rings[0]) as *const TopoRing<u32> ]).unwrap();
        let edge2 = edges.iter().find(|e| e.rings == vec![ &(*normal.regions[1].outer_rings[0]) as *const TopoRing<u32> ]).unwrap();
        assert_eq!(vec![ Point(1, 2), Point(1, 1), Point(2, 1) ], edge_to_points(&edge1));
        // edge2 is reversed in its ring.
        assert_eq!(vec![ Point(1, 2), Point(2, 2), Point(2, 1) ], edge_to_points(&edge2));
        let edge12 = edges.iter().find(|e| e.rings.len() == 2).unwrap();
        assert_eq!(vec![ Point(1, 2), Point(2, 1) ], edge_to_points(&edge12));
    }

    #[test]
    fn flatten_common_edges() {
        let mut builder = TopologyBuilder::<u32>::new();

        // *---*
        // |\1/|
        // | * |
        // | 2 |
        // *---*
        builder.add_region(&Region {
            data: 1,
            outer_rings: vec![ Ring::Points(vec![ Point(1, 1), Point(3, 1), Point(2, 2), Point(1, 1) ].into_boxed_slice()) ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice(),
        });
        builder.add_region(&Region {
            data: 2,
            outer_rings: vec![ Ring::Points(vec![ Point(1, 1), Point(2, 2), Point(3, 1), Point(3, 3), Point(1, 3), Point(1, 1) ].into_boxed_slice()) ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice(),
        });

        let topology = builder.into_topology();
        let normal = normalize(&topology);

        assert_eq!(3, normal.edges.len());
        let edges: Vec<&TopoEdge<_>> = normal.edges.iter().map(|e| &**e).collect();
        let edge1 = edges.iter().find(|e| e.rings == vec![ &(*normal.regions[0].outer_rings[0]) as *const TopoRing<u32> ]).unwrap();
        let edge2 = edges.iter().find(|e| e.rings == vec![ &(*normal.regions[1].outer_rings[0]) as *const TopoRing<u32> ]).unwrap();
        let edge12 = edges.iter().find(|e| e.rings.len() == 2).unwrap();
        assert_eq!(vec![ Point(1, 1), Point(3, 1) ], edge_to_points(&edge1));
        assert_eq!(vec![ Point(1, 1), Point(1, 3), Point(3, 3), Point(3, 1) ], edge_to_points(&edge2));
        assert_eq!(vec![ Point(1, 1), Point(2, 2), Point(3, 1) ], edge_to_points(&edge12));
    }

    #[test]
    fn rotate_island() {
        let mut builder = TopologyBuilder::<()>::new();
        builder.add_region(&Region {
            data: (),
            outer_rings: vec![ Ring::Points(vec![ Point(2, 1), Point(1, 2), Point(1, 1), Point(2, 1) ].into_boxed_slice()) ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice(),
        });

        let topology = builder.into_topology();
        let normal = normalize(&topology);

        assert_eq!(1, normal.edges.len());
        let edge: &TopoEdge<_> = &*normal.edges[0];
        assert_eq!(vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ], edge_to_points(&edge));
    }

    #[test]
    fn rotate_rings() {
        let mut builder = TopologyBuilder::<u32>::new();

        //  *---*
        //  |\1/|
        // /  * |
        // |  2 |
        // *----*
        builder.add_region(&Region {
            data: 1,
            outer_rings: vec![ Ring::Points(vec![ Point(3, 2), Point(2, 1), Point(4, 1), Point(3, 2) ].into_boxed_slice()) ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice(),
        });
        builder.add_region(&Region {
            data: 2,
            outer_rings: vec![ Ring::Points(vec![ Point(3, 2), Point(4, 1), Point(4, 3), Point(1, 3), Point(2, 1), Point(3, 2) ].into_boxed_slice()) ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice(),
        });

        let topology = builder.into_topology();
        let normal = normalize(&topology);

        assert_eq!(3, normal.edges.len());
        let ref dedge11 = normal.regions[0].outer_rings[0].directed_edges[0];
        let ref dedge12 = normal.regions[0].outer_rings[0].directed_edges[1];
        let ref dedge21 = normal.regions[1].outer_rings[0].directed_edges[0];
        let ref dedge22 = normal.regions[1].outer_rings[0].directed_edges[1];

        assert_eq!(vec![ Point(2, 1), Point(4, 1) ], edge_to_points(unsafe { &*dedge11.edge }));
        assert_eq!(vec![ Point(2, 1), Point(3, 2), Point(4, 1) ], edge_to_points(unsafe { &*dedge12.edge }));
        assert_eq!(dedge12.edge, dedge21.edge);
        assert_eq!(vec![ Point(2, 1), Point(1, 3), Point(4, 3), Point(4, 1) ], edge_to_points(unsafe { &*dedge22.edge }));
    }

    #[test]
    fn nix_redundant_edges() {
        let mut builder = TopologyBuilder::<()>::new();

        // *--* *--*
        // | /| | /
        // |/ | |/
        // *--* *
        builder.add_region(&Region {
            data: (),
            outer_rings: vec![
                Ring::Points(vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ].into_boxed_slice()),
                Ring::Points(vec![ Point(2, 1), Point(2, 2), Point(1, 2), Point(2, 1) ].into_boxed_slice()),
                Ring::Points(vec![ Point(3, 1), Point(4, 1), Point(3, 2), Point(3, 1) ].into_boxed_slice()),
            ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice(),
        });

        let topology = builder.into_topology();
        let normal = normalize(&topology);

        let ref dedge1 = normal.regions[0].outer_rings[0].directed_edges[0];
        let ref dedge2 = normal.regions[0].outer_rings[1].directed_edges[0];

        assert_eq!(vec![ Point(1, 1), Point(2, 1), Point(2, 2), Point(1, 2), Point(1, 1) ], edge_to_points(unsafe { &*dedge1.edge }));
        assert_eq!(vec![ Point(3, 1), Point(4, 1), Point(3, 2), Point(3, 1) ], edge_to_points(unsafe { &*dedge2.edge }));
    }

    #[test]
    fn order_rings() {
        let mut builder = TopologyBuilder::<()>::new();

        let first = vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ];
        let second = vec![ Point(3, 1), Point(4, 1), Point(3, 2), Point(3, 1) ];

        // *--* *--*
        // | /  | /
        // |/   |/
        // *    *
        builder.add_region(&Region {
            data: (),
            outer_rings: vec![ Ring::Points(second.clone().into_boxed_slice()), Ring::Points(first.clone().into_boxed_slice()) ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice(),
        });

        let topology = builder.into_topology();
        let normal = normalize(&topology);

        let ref dedge1 = normal.regions[0].outer_rings[0].directed_edges[0];
        let ref dedge2 = normal.regions[0].outer_rings[1].directed_edges[0];

        assert_eq!(first, edge_to_points(unsafe { &*dedge1.edge }));
        assert_eq!(second, edge_to_points(unsafe { &*dedge2.edge }));
    }

    #[test]
    fn clockwise_outer_ring() {
        let mut builder = TopologyBuilder::<()>::new();

        // A--C
        // | /
        // |/
        // B
        builder.add_region(&Region {
            data: (),
            outer_rings: vec![ Ring::Points(vec![ Point(1, 1), Point(1, 2), Point(2, 1), Point(1, 1) ].into_boxed_slice()) ].into_boxed_slice(),
            inner_rings: vec![].into_boxed_slice(),
        });

        let topology = builder.into_topology();
        let normal = normalize(&topology);

        assert_eq!(1, normal.edges.len());
        let ref dedge = normal.regions[0].outer_rings[0].directed_edges[0];
        assert_eq!(Direction::Forward, dedge.direction);
        assert_eq!(
            vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ],
            edge_to_points(unsafe { &*dedge.edge })
        );
    }

    #[test]
    fn counter_clockwise_inner_ring() {
        let mut builder = TopologyBuilder::<()>::new();

        // A----B
        // |D-E/
        // ||//
        // |F/
        // |/
        // C
        builder.add_region(&Region {
            data: (),
            outer_rings: vec![ Ring::Points(vec![ Point(1, 1), Point(4, 1), Point(1, 4), Point(1, 1) ].into_boxed_slice()) ].into_boxed_slice(),
            inner_rings: vec![ Ring::Points(vec![ Point(2, 2), Point(3, 2), Point(2, 3), Point(2, 2) ].into_boxed_slice()) ].into_boxed_slice(),
        });

        let topology = builder.into_topology();
        let normal = normalize(&topology);

        assert_eq!(2, normal.edges.len());

        let ref dedge1 = normal.regions[0].outer_rings[0].directed_edges[0];
        assert_eq!(Direction::Forward, dedge1.direction);

        let ref dedge2 = normal.regions[0].inner_rings[0].directed_edges[0];
        assert_eq!(Direction::Backward, dedge2.direction);
        assert_eq!(
            vec![ Point(2, 2), Point(3, 2), Point(2, 3), Point(2, 2) ],
            edge_to_points(unsafe { &*dedge2.edge })
        );
    }

    #[test]
    fn nix_donut() {
        let mut builder = TopologyBuilder::<()>::new();

        // A----B
        // |D-E/
        // ||//
        // |F/
        // |/
        // C
        builder.add_region(&Region {
            data: (),
            outer_rings: vec![
                Ring::Points(vec![ Point(1, 1), Point(4, 1), Point(1, 4), Point(1, 1) ].into_boxed_slice()),
                Ring::Points(vec![ Point(2, 2), Point(2, 3), Point(3, 2), Point(2, 2) ].into_boxed_slice()),
            ].into_boxed_slice(),
            inner_rings: vec![
                Ring::Points(vec![ Point(2, 2), Point(3, 2), Point(2, 3), Point(2, 2) ].into_boxed_slice()),
            ].into_boxed_slice(),
        });

        let topology = builder.into_topology();
        let normal = normalize(&topology);

        assert_eq!(1, normal.edges.len());

        let ref dedge = normal.regions[0].outer_rings[0].directed_edges[0];
        assert_eq!(Direction::Forward, dedge.direction);
        assert_eq!(
            vec![ Point(1, 1), Point(4, 1), Point(1, 4), Point(1, 1) ],
            edge_to_points(unsafe { &*dedge.edge })
        );
    }
}
