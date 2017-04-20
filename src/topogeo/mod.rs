pub mod geo;
pub mod topology;
pub mod normalize;
//pub mod read;

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
pub struct Point(pub u32, pub u32);
