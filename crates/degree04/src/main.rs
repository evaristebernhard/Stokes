fn main() {
    println!("Kummer quartic over Q(sqrt(2))");
    println!("nodes = {}", degree04::kummer_node_count());
    println!(
        "affine gradient candidates = {}, affine surface singular candidates = {}",
        degree04::affine_gradient_candidate_count(),
        degree04::affine_surface_singular_candidate_count()
    );
    println!(
        "no singular points at infinity = {}",
        degree04::infinity_chart_certificate().no_singular_points()
    );
    println!("tropes = {}", degree04::kummer_tropes().len());

    for verification in degree04::kummer_node_verifications() {
        println!("  {verification}");
    }
}
