// The language item is deliberately gated even though the hidden macro shim
// is present in the standard library.
join impl NoFeature { //~ ERROR join-calculus syntax is experimental
    channel value(input: u32) -> u32;
    when value(input) {
        return { value: input };
    }
}

fn main() {}
