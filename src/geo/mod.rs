use std::fmt;
use itertools::Itertools;

/// Point is comparable so TopoEdge can have a canonical direction (top-left to
/// bottom-right, conceptually). That helps us build EdgeSet without checking
/// two directions.
#[derive(Clone, Copy, Debug, Hash, Ord, Eq, PartialEq, PartialOrd)]
pub struct Point(pub u32, pub u32);

impl fmt::Display for Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({},{})", self.0, self.1)
    }
}

/// A path joining two Points, via any number of intermediate Points.
#[derive(Clone,Debug)]
pub struct Edge(pub Box<[Point]>);

impl fmt::Display for Edge {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut ret = write!(f, "Edge(");
        for (i, point) in self.0.iter().enumerate() {
            if i > 0 {
                ret = ret.and_then(|_| write!(f, ","));
            }
            ret = ret.and_then(|_| write!(f, "{}", point));
        }
        ret.and_then(|_| write!(f, ")"))
    }
}

/// A path joining a Point to itself, totalling three or more Points.
///
/// Clockwise means positive space (regions); counter-clockwise means negative
/// space (holes).
///
/// Beware self-intersecting Rings. Some algorithms require Rings not to
/// intersect themselves. We don't strictly enforce that rule, because
/// projecting a Ring into a new coordinate space can break the assumption.
#[derive(Clone,Debug)]
pub enum Ring {
    /// Efficient for geometry-related algorithms.
    Points(Box<[Point]>),

    /// Efficient for topology-related algorithms.
    Edges(Box<[Edge]>),
}

impl fmt::Display for Ring {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut ret = write!(f, "[");
        match self {
            &Ring::Points(ref points) => {
                for (i, point) in points.iter().enumerate() {
                    if i > 0 {
                        ret = ret.and_then(|_| write!(f, ","));
                    }
                    ret = ret.and_then(|_| write!(f, "{}", point));
                }
            },
            &Ring::Edges(ref edges) => {
                for (i, edge) in edges.iter().enumerate() {
                    if i > 0 {
                        ret = ret.and_then(|_| write!(f, ","));
                    }
                    ret = ret.and_then(|_| write!(f, "{}", edge));
                }
            }
        }
        ret.and_then(|_| write!(f, "]"))
    }
}

#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum WindingOrder {
    Clockwise,
    CounterClockwise,
}

impl Ring {
    /// Returns all Points in the Ring, in order, copied.
    pub fn points(&self) -> Box<[Point]> {
        match self {
            &Ring::Points(ref points) => points.clone(),
            &Ring::Edges(ref edges) => {
                let len = edges.iter().map(|e| e.0.len()).sum();
                let mut ret = Vec::<Point>::with_capacity(len);
                for ref edge in edges.iter() {
                    ret.extend_from_slice(&*edge.0);
                }
                ret.into_boxed_slice()
            }
        }
    }

    /// Returns all Edges in the Ring, in order.
    pub fn edges(&self) -> Box<[Edge]> {
        match self {
            &Ring::Edges(ref edges) => edges.clone(),
            &Ring::Points(ref points) => {
                let ret: Vec<Edge> = points.iter().tuple_windows()
                    .map(|(&p1, &p2)| Edge(vec![ p1, p2 ].into_boxed_slice()))
                    .collect();
                ret.into_boxed_slice()
            }
        }
    }

    /// Returns 2*area
    pub fn area2(&self) -> u64 {
        self.area2_and_winding_order().0
    }

    /// Returns 2*area and winding order.
    ///
    /// Assumes (0,0) is the **top left** coordinate. In other words, this isn't
    /// WGS84 (in which north is positive): it's like SVG or HTML5 <canvas>
    /// coordinates.
    ///
    /// A zero-area Ring is considered to be Clockwise.
    pub fn area2_and_winding_order(&self) -> (u64, WindingOrder) {
        let points = self.points();

        assert!(points.len() > 2);
        assert!(points.first() == points.last());

        // https://en.wikipedia.org/wiki/Shoelace_formula
        let mut a: i64 = 0;

        for (p1, p2) in points.iter().tuple_windows() {
            a += (p1.0 as i64) * (p2.1 as i64) - (p2.0 as i64) * (p1.1 as i64)
        }

        if a >= 0 {
            (a as u64, WindingOrder::Clockwise)
        } else {
            (-a as u64, WindingOrder::CounterClockwise)
        }
    }

    /// Returns winding order.
    ///
    /// Assumes (0,0) is the **top left** coordinate. In other words, this isn't
    /// WGS84 (in which north is positive): it's like SVG or HTML5 <canvas>
    /// coordinates.
    ///
    /// A zero-area Ring is considered to be Clockwise.
    pub fn winding_order(&self) -> WindingOrder {
        self.area2_and_winding_order().1
    }
}

#[derive(Debug)]
pub struct Region<Data> {
    pub data: Data,
    pub outer_rings: Box<[Ring]>,
    pub inner_rings: Box<[Ring]>,
}

struct DisplayRings<'a>(&'a [Ring]);
impl<'a> fmt::Display for DisplayRings<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut ret = write!(f, "[");
        for (i, ref ring) in self.0.iter().enumerate() {
            if i > 0 {
                ret = ret.and_then(|_| write!(f, ", "));
            }
            ret = ret.and_then(|_| write!(f, "{}", ring));
        }
        ret.and_then(|_| write!(f, "]"))
    }
}

impl<Data> fmt::Display for Region<Data> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let outer = DisplayRings(&*self.outer_rings);
        let inner = DisplayRings(&*self.inner_rings);
        write!(f, "Region([data], outer:{}, inner:{})", outer, inner)
    }
}

#[cfg(Test)]
mod test {
    #[test]
    fn test_edge_ring_edges() {
        let edges = vec![
            Edge(vec![ Point(1, 1), Point(1, 2), Point(2, 1) ].into_boxed_slice()),
            Edge(vec![ Point(2, 1), Point(1, 1) ].into_boxed_slice()),
        ].into_boxed_slice();
        let ring: Ring = Ring::Edges(edges);
        assert_eq!(edges, ring.edges());
    }

    #[test]
    fn test_edge_ring_points() {
        let ring: Ring = Ring::Edges(vec![
            Edge(vec![ Point(1, 1), Point(1, 2), Point(2, 1) ].into_boxed_slice()),
            Edge(vec![ Point(2, 1), Point(1, 1) ].into_boxed_slice()),
        ].into_boxed_slice());
        assert_eq!(vec![ Point(1, 1), Point(1, 2), Point(2, 1), Point(1, 1) ].into_boxed_slice(), ring.points());
    }

    #[test]
    fn test_point_ring_edges() {
        let ring = Ring::Points(vec![ Point(1, 1), Point(1, 2), Point(2, 1), Point(1, 1) ].into_boxed_slice());
        assert_eq!(vec![
            Edge(vec! [ Point(1, 1), Point(1, 2) ].into_boxed_slice()),
            Edge(vec! [ Point(1, 2), Point(2, 1) ].into_boxed_slice()),
            Edge(vec! [ Point(2, 1), Point(1, 1) ].into_boxed_slice()),
        ].into_boxed_slice(), ring.edges());
    }

    #[test]
    fn test_point_ring_points() {
        let points = vec![ Point(1, 1), Point(1, 2), Point(2, 1), Point(1, 1) ].into_boxed_slice();
        let ring = Ring::Points(points);
        assert_eq!(points, ring.points());
    }
}
