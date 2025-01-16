To run this code you first have to generate three files for a particular universe size(n) named "secret_keysn.bin","hints_test_datan.bin" and "setup_requirementsn.bin" 
that consists of all the one time computations for a whole universe.You have to run cargo test -- release "generate_hints_and_sks_for_n" and 
cargo test --release "generate_hints_independents_n_mult" for your particular n.
Then run "cargo run --release universe_size committee_size threshold" according to your inputs.

For example, lets take universe size (n) = 1024, committee size(c) = 64, threshold = 23, you have to run the following commands

cargo test --release generate_hints_and_sks_for_1024
cargo test --release generate_hints_independents_1024_mult
cargo run --release 1024 64 23
