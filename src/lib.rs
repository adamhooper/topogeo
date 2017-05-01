extern crate byteorder;
extern crate encoding;
extern crate itertools;
#[macro_use] extern crate lazy_static;
extern crate regex;

pub mod geo;
pub mod topology;
mod normalize;
mod simplify;
pub mod read;

pub use normalize::normalize;
pub use simplify::simplify;
