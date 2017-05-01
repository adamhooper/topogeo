use std::cmp;
use std::ptr;
use geo;

fn area2(a: &geo::Point, b: &geo::Point, c: &geo::Point) -> u64 {
    fn i(u: u32) -> i64 { u as i64 }
    let a2: i64 = (i(b.0) * i(a.0)) * (i(c.1) - i(a.1)) - (i(c.0) - i(a.0)) * (i(b.1) - i(a.1));
    a2.abs() as u64
}

#[derive(Debug)]
struct Point {
    /// The point's place in space.
    geo_point: geo::Point,

    /// The "importance" of the point. This is the "output" of Visvalingam and
    /// Whyatt's algorithm. We'll only keep points above a certain weight. (the
    /// first and last point have maximum weight.)
    weight: u64,

    /// Position in a binary heap (minimum weight first).
    heap_index: usize,

    /// Position in a linked list (unvisited points, in order).
    ///
    /// When we remove a point from the heap and linked list, we'll recalculate
    /// the weights of its siblings.
    next: *const Point,
    previous: *const Point,
}

impl PartialEq for Point {
    fn eq(&self, other: &Self) -> bool {
        self.weight.eq(&other.weight)
    }
}

impl Eq for Point {}

impl PartialOrd for Point {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.weight.partial_cmp(&other.weight)
    }
}

impl Ord for Point {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.weight.cmp(&other.weight)
    }
}

#[derive(Debug)]
struct PointHeap {
    points: Vec<Point>,
    heap: Vec<*const Point>,
}

impl From<Vec<geo::Point>> for PointHeap {
    fn from(vec: Vec<geo::Point>) -> PointHeap {
        let len = vec.len();
        assert!(len >= 2);

        let is_ring = vec[0] == vec[len - 1];
        assert!(!is_ring || len >= 4);

        let mut points: Vec<Point> = vec.into_iter()
            .map(|p| Point {
                geo_point: p,
                heap_index: 0,
                weight: 0,
                next: ptr::null(),
                previous: ptr::null(),
            })
            .collect();

        points[0].weight = u64::max_value();
        points[0].next = &points[1];
        points[len - 1].weight = u64::max_value();
        points[len - 1].previous = &points[len - 2];

        // Compute initial weights
        for i in 1 .. len - 1 {
            let area2 = area2(&points[i - 1].geo_point, &points[i].geo_point, &points[i + 1].geo_point);

            points[i].weight = area2;
            points[i].next = &points[i + 1];
            points[i].previous = &points[i - 1];
        }

        let heap = points[1 .. points.len() - 1].iter().map(|p| p as *const Point).collect();

        let mut ret = PointHeap {
            points: points,
            heap: heap,
        };
        ret.heapify();
        ret
    }
}

fn parent(i: usize) -> usize {
    (i - 1) / 2
}

fn left_child(i: usize) -> usize {
    2 * i + 1
}

/// A min-heap of mutable Points.
///
/// It's an unsafe, hacky paradise.
impl PointHeap {
    fn heapify(&mut self) {
        // https://en.wikipedia.org/wiki/Heapsort
        let len = self.heap.len();

        if len > 1 {
            let mut start = parent(len - 1);

            loop {
                self.sift_down(start, len - 1);
                if start == 0 {
                    break;
                }
                start -= 1;
            }
        }
    }

    fn sift_down(&mut self, start: usize, end: usize) {
        let mut root: usize = start;

        while left_child(root) <= end {
            let child = left_child(root);
            let mut swap = root;

            if unsafe { *self.heap[start] > *self.heap[child] } {
                swap = child;
            }

            if child +1 <= end && unsafe { *self.heap[swap] > *self.heap[child + 1] } {
                swap = child + 1;
            }

            if swap == root {
                // root holds smallest element
                return;
            } else {
                // Swap the pointers
                self.swap(root, swap);
                root = swap;
            }
        }
    }

    fn sift_up(&mut self, start: usize, end: usize) {
        let mut child = end;

        while child > start {
            let parent = parent(child);
            if unsafe { *self.heap[parent] > *self.heap[child] } {
                // out of heap order; swap the pointers
                self.swap(parent, child);
                child = parent;
            } else {
                return;
            }
        }
    }

    fn swap(&mut self, a: usize, b: usize) {
        self.heap.swap(a, b);
        unsafe {
            (*(self.heap[a] as *const Point as *mut Point)).heap_index = a;
            (*(self.heap[b] as *const Point as *mut Point)).heap_index = b;
        }
    }

    /// Removes and returns the smallest-weight Point in the heap.
    ///
    /// # Panics
    ///
    /// Panics if the heap is empty.
    fn pop(&mut self) -> *mut Point {
        let len = self.heap.len();

        assert!(len >= 1);

        if len == 1 {
            self.heap.pop().unwrap() as *mut Point
        } else {
            let top: *mut Point = self.heap[0] as *mut Point;
            let last: *mut Point = self.heap.pop().unwrap() as *mut Point;
            self.heap[0] = last;
            unsafe { (*last).heap_index = 0; }
            self.sift_down(0, len - 2);

            unsafe {
                (*((*top).previous as *mut Point)).next = (*top).next;
                (*((*top).next as *mut Point)).previous = (*top).previous;
            }

            top
        }
    }

    /// Changes the weight of the Point we point to, and adjusts the heap to
    /// match.
    ///
    /// Call this after tweaking the linked list of Points.
    fn recalculate_point_weight(&mut self, point_ptr: *mut Point) {
        let mut b: &mut Point = unsafe { &mut *point_ptr };

        match unsafe { (b.previous.as_ref(), b.next.as_ref()) } {
            (Some(a), Some(c)) => {
                let new_weight = area2(&a.geo_point, &b.geo_point, &c.geo_point);

                // In-place heap modification.
                if new_weight < b.weight {
                    // We're making b.weight _smaller_. That means it may be
                    // smaller than its parent. (It won't become smaller than
                    // its children, because it originally was larger.)
                    b.weight = new_weight;
                    self.sift_up(0, b.heap_index);
                } else if new_weight > b.weight {
                    // We're making b.weight _larger_. That means it may be
                    // larger than its child. (It won't become smaller than its
                    // parent, because it originally was smaller.)
                    b.weight = new_weight;
                    let len = self.heap.len();
                    self.sift_down(b.heap_index, len - 1);
                }
            }
            _ => {
                // We're at the first or last point. Their weight can't change.
                return;
            }
        }
    }

    /// Returns only the geo::Points worth keeping.
    ///
    /// Modifies self.points[*].weight using a priority queue:
    ///
    /// 1. remove the smallest-weight point: its weight is correct
    /// 2. recalculate the weights of the points before and after it,
    ///    now that it's gone
    /// 3. repeat until we know all the remaining points' weights are large
    ///    enough to include.
    ///
    /// Other side-effects: fiddles with self.heap and self.points[*].heap_index
    fn visvalingam_whyatt(&mut self, smallest_weight: u64) -> Box<[geo::Point]> {
        let mut last_weight = 0; // weight of previously-eliminated point

        while self.heap.len() > 0 {
            let p: *mut Point = self.pop();
            let small_point: &mut Point = unsafe { &mut *p };

            // If its calculated area is less than that of the last point to be eliminated,
            // use the latter's area instead. (This ensures that the current point cannot
            // be eliminated without eliminating previously eliminated points.)
            if small_point.weight < last_weight {
                small_point.weight = last_weight;
            } else {
                if small_point.weight >= smallest_weight {
                    // We don't need to figure out the exact weight of
                    // any more points, because we know we aren't going to
                    // remove them when we simplify. (Their weights are
                    // all above our `smallest_weight` threshold.)
                    break;
                }

                last_weight = small_point.weight; // for next iteration
            }

            if !small_point.previous.is_null() {
                self.recalculate_point_weight(small_point.previous as *mut Point);
            }
            if !small_point.next.is_null() {
                self.recalculate_point_weight(small_point.next as *mut Point);
            }
        }

        let mut ret: Vec<geo::Point> = self.points.iter()
            .filter(|ref p| p.weight >= smallest_weight)
            .map(|ref p| p.geo_point)
            .collect();

        // Do not change topology: a ring must remain a ring. That means a
        // triangle at least -- four points (1st and 4th points identical).
        let is_ring = ret[0] == ret[ret.len() - 1];
        if is_ring && ret.len() < 4 {
            // Find the two highest-weight points
            let mut first: &Point = &self.points[1];
            let mut second: &Point = &self.points[2];
            let mut first_has_lower_index = true;

            if second.weight > first.weight {
                let t: &Point = first;
                first = second;
                second = t;
                first_has_lower_index = false;
            }

            for ref point in &self.points[3 .. self.points.len() - 1] {
                if point.weight > first.weight {
                    second = first;
                    first = point;
                    first_has_lower_index = false;
                } else if point.weight > second.weight {
                    second = point;
                    first_has_lower_index = true;
                }
            }

            let (p1, p2) = if first_has_lower_index {
                (first, second)
            } else {
                (second, first)
            };

            ret = vec![
                self.points[0].geo_point,
                p1.geo_point,
                p2.geo_point,
                self.points[self.points.len() - 1].geo_point
            ];
        }

        ret.into_boxed_slice()
    }
}

/// Returns a simpler version of the given edge.
///
/// smallest_area2 is 2x the smallest area we want to morph the line by when
/// removing a point. The 2x makes for fast math -- and it's easy to understand
/// because it's in terms of rectangles. For instance, if you want to err by
/// "at most one pixel" and coordinates are pixels, set `smallest_area2` to `1`.
pub fn simplify_edge(points: &[geo::Point], smallest_area2: u64) -> Box<[geo::Point]> {
    let mut point_heap = PointHeap::from(points.to_vec());
    point_heap.visvalingam_whyatt(smallest_area2)
}

#[cfg(test)]
mod test {
    use geo::Point;
    use super::simplify_edge;

    fn go(points: &[Point], a: u64) -> Vec<Point> {
        simplify_edge(points, a).into_vec()
    }

    #[test]
    fn two_points_not_changed() {
        assert_eq!(vec![ Point(1, 1), Point(2, 2) ], go(&[ Point(1, 1), Point(2, 2) ], 1));
    }

    #[test]
    fn three_points_to_two() {
        // empty heap
        assert_eq!(
            vec![ Point(1, 1), Point(2, 2) ],
            go(&[ Point(1, 1), Point(1, 10), Point(2, 2) ], 9)
        );
    }

    #[test]
    fn three_points_to_three() {
        // one-element heap
        assert_eq!(
            vec![ Point(1, 1), Point(1, 10), Point(2, 2) ],
            go(&[ Point(1, 1), Point(1, 10), Point(2, 2) ], 8)
        );
    }

    #[test]
    fn four_points_to_three() {
        // two-element heap
        assert_eq!(
            vec![ Point(1, 1), Point(1, 10), Point(2, 2) ],
            go(&[ Point(1, 1), Point(1, 10), Point(2, 1), Point(2, 2) ], 8)
        );
    }

    #[test]
    fn ring_has_min_four_points() {
        assert_eq!(
            vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ],
            go(&[ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ], 10)
        );
    }

    #[test]
    fn ring_has_over_four_points() {
        assert_eq!(
            vec![ Point(1, 1), Point(3, 1), Point(3, 3), Point(1, 3), Point(1, 1) ],
            go(&[ Point(1, 1), Point(3, 1), Point(3, 3), Point(1, 3), Point(1, 1) ], 3)
        );
    }
}
