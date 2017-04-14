#[cfg(test)]
use topogeo::topology::Topology;
#[cfg(test)]
use topogeo::topology::TopologyBuilder;

#[cfg(test)]
pub fn normalize<Data>(topo: &Topology<Data>) -> Topology<Data> {
    let builder = TopologyBuilder::<Data>::new();

    builder.into_topology()
}

#[cfg(test)]
mod test {
}
