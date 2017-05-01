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
