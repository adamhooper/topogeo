# topogeo
Fast geometry parsing, simplification and output

This is a Rust library with an awfully-specific goal: build an
enormous set of vector map tiles of Canadian census dissemination
blocks.

## Features

* Parses a (projected) Shapefile and stores it internally as `u32` coordinates.
  (This is much simpler and faster -- and more restrictive -- than
  [rust-geo](https://github.com/georust/rust-geo).)
* Converts to an internal topology format, using shared edges.
* Simplifies topology, using Visvalingam simplification, without changing topology.
* [ ] Filters out tiny areas.
* [ ] Merges topological regions into parent ones, to support "zoom-out" coarser
  level of detail.
* [ ] Clips a topology into slightly-overlapping tiles.
* [ ] Reads and writes a simple binary format that encodes topology. (It's like topojson,
  but easier to parse and faster.)
  
With inconsequential exceptions, operations scale [O(n)](https://en.wikipedia.org/wiki/Time_complexity#Linear_time)
with the input size.

## Installation

This is a work-in-progress, so all you can run are example scripts. Here's how
I'm running them:

1. Install [rust](https://www.rust-lang.org). Using [rustup](https://www.rustup.rs/):
   `curl https://sh.rustup.rs -sSf | sh`
2. `git clone https://github.com/adamhooper/topogeo.git && cd topogeo`
3. `cargo build --release`

Try out the examples in `examples/`. To build one:
`rustc -O -g -L target/release -L target/release/deps examples/shp-to-geo-data.rs`

Basically, I keep running something like this on my command line:

```sh
cargo build --release && \
  rustc -O -g -L target/release -L target/release/deps examples/shp-to-geo-data.rs && \
  echo 'compiled' && \
  RUST_BACKTRACE=1 time ./shp-to-geo-data ~/Downloads/ldb_000b16a_e/ldb_000b16a_e.shp`
```

## Developing

You can run unit tests whenever code changes:

1. `cargo install cargo-watch`
2. `RUST_BACKTRACE=1 cargo watch -x check -x test`

# License

[Public Domain](https://creativecommons.org/publicdomain/zero/1.0/): To the extent
possible under law, Adam Hooper has waived all copyright and related or neighboring
rights to topogeo. This work is published from: Canada.
