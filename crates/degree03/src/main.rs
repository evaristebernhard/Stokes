fn main() {
    println!("Cayley cubic: xyz + xyw + xzw + yzw = 0 in P^3");
    println!("nodes = {}", degree03::cayley_node_count());

    for verification in degree03::cayley_node_verifications() {
        println!("  {verification}");
    }
}
