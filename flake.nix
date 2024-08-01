{
  description = "Test dafny projects";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { config, self', inputs', pkgs, system, ... }: {
        packages.default = pkgs.writeShellScriptBin "dafny-test-all" ''
            for f in *.dfy
            do
                echo "Testing $f"
                ${pkgs.dafny}/bin/dafny verify --allow-warnings --verification-time-limit 10 $f
            done
        '';
      };
    };
}
