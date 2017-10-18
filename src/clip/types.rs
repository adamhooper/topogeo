use geo::Point;

/// Determines how to clip.
///
/// Each clip operation works along one axis: either the X axis or the Y
/// axis.
#[derive(Debug)]
pub enum ClipMask {
    MinX(u32),
    MaxX(u32),
    MinY(u32),
    MaxY(u32),
}

#[derive(Debug,PartialEq,Eq)]
pub enum ClipLocation {
    Inside,
    OnEdge,
    Outside,
}

impl ClipMask {
    /// Returns whether the given point is inside, on the edge, or outside
    /// of this mask.
    pub fn test(&self, point: &Point) -> ClipLocation {
        // Handle on-edge
        match self {
            &ClipMask::MinX(x) | &ClipMask::MaxX(x) => {
                if point.0 == x { return ClipLocation::OnEdge; }
            },
            &ClipMask::MinY(y) | &ClipMask::MaxY(y) => {
                if point.1 == y { return ClipLocation::OnEdge; }
            },
        }

        fn t(inside: bool) -> ClipLocation {
            if inside { ClipLocation::Inside } else { ClipLocation::Outside }
        }

        match self {
            &ClipMask::MinX(x) => t(point.0 >= x),
            &ClipMask::MaxX(x) => t(point.0 <= x),
            &ClipMask::MinY(y) => t(point.1 >= y),
            &ClipMask::MaxY(y) => t(point.1 <= y),
        }
    }

    /// Returns the `Point` along the edge of this clip mask when you follow a
    /// straight line from `p1` to `p2`.
    ///
    /// Assumes either `p1` or `p2` is outside the clip mask.
    pub fn intersect(&self, p1: &Point, p2: &Point) -> Point {
        fn i(u: u32) -> i64 { u as i64 }

        match self {
            &ClipMask::MinX(x) | &ClipMask::MaxX(x) => {
                let y = i(p1.1) + (i(x) - i(p1.0)) * (i(p2.1) - i(p1.1)) / (i(p2.0) - i(p1.0));
                Point(x, y as u32)
            }
            &ClipMask::MinY(y) | &ClipMask::MaxY(y) => {
                let x = i(p1.0) + (i(y) - i(p1.1)) * (i(p2.0) - i(p1.0)) / (i(p2.1) - i(p1.1));
                Point(x as u32, y)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use geo::Point;
    use super::{ClipLocation, ClipMask};

    #[test]
    fn test_min_x() {
        let mask = ClipMask::MinX(100);
        assert_eq!(ClipLocation::Inside, mask.test(&Point(101, 99)));
        assert_eq!(ClipLocation::OnEdge, mask.test(&Point(100, 101)));
        assert_eq!(ClipLocation::Outside, mask.test(&Point(99, 101)));
    }

    #[test]
    fn test_max_x() {
        let mask = ClipMask::MaxX(100);
        assert_eq!(ClipLocation::Inside, mask.test(&Point(99, 101)));
        assert_eq!(ClipLocation::OnEdge, mask.test(&Point(100, 1)));
        assert_eq!(ClipLocation::Outside, mask.test(&Point(101, 1)));
    }

    #[test]
    fn test_min_y() {
        let mask = ClipMask::MinY(100);
        assert_eq!(ClipLocation::Inside, mask.test(&Point(99, 101)));
        assert_eq!(ClipLocation::OnEdge, mask.test(&Point(101, 100)));
        assert_eq!(ClipLocation::Outside, mask.test(&Point(101, 99)));
    }

    #[test]
    fn test_max_y() {
        let mask = ClipMask::MaxY(100);
        assert_eq!(ClipLocation::Inside, mask.test(&Point(101, 99)));
        assert_eq!(ClipLocation::OnEdge, mask.test(&Point(1, 100)));
        assert_eq!(ClipLocation::Outside, mask.test(&Point(1, 101)));
    }
}
