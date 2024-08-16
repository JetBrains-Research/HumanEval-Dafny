{
  description = "Test dafny projects";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { pkgs, ... }: {
        packages = {
          dafny-check = pkgs.writeShellScriptBin "dafny-check" ''
            DIR=''${1:-.}
            for f in "$DIR"/*.dfy
            do
                ${pkgs.dafny}/bin/dafny verify --allow-warnings --verification-time-limit 2400 $f || exit 1
            done
          '';

          dafny-namecheck = pkgs.writeShellScriptBin "dafny-namecheck" ''
            # Directory to check, use current directory if not specified
            DIR=''${1:-.}

            for file in "$DIR"/*.dfy; do
              if [[ -e $file ]]; then
                filename=$(basename "$file")

                if ! [[ $filename =~ ^[0-9]{3} ]]; then
                  echo "File $file does not start with three digits. (this is needed for better sorting)"
                  exit 1
                fi
              fi
            done

            echo "All dafny files start with three digits."
          '';
        };
      };
    };
}
