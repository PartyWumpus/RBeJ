{
	inputs = {
		flake-utils.url = "github:numtide/flake-utils";
		nixpkgs.url = "github:nixos/nixpkgs";

		rust-overlay.url = "github:oxalica/rust-overlay";
	};

	outputs = {
		self,
		nixpkgs,
		flake-utils,
		rust-overlay,
		...
	}:
		flake-utils.lib.eachDefaultSystem (system:
			let
				pkgs = import nixpkgs {
					inherit system;
					overlays = [ (import rust-overlay) ];
				};
			in with pkgs; rec {
				devShell = mkShell rec {
					packages = [
						rust-bin.stable.latest.default
						#(rust-bin.fromRustupToolchainFile ./rust-toolchain)

            llvm_18
            libffi
            libxml2
            linuxPackages_latest.perf
					];
					#LD_LIBRARY_PATH = "${lib.makeLibraryPath buildInputs}";
				};
        shellHook = ''
          export RUSTFLAGS='-C target-cpu=native'
        '';
			});
}
