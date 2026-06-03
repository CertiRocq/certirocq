{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/rocq-overlays`
  ## and `.nix/coq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "CertiRocq";

  no-rocq-yet = true;

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  # pname = "{{shortname}}";

  default-bundle = "default";
  ## When generating GitHub Action CI, one workflow file
  ## will be created per bundle
  bundles."default" = { coqPackages = {
      coq.override.version = "9.1";
      compcert.job = false;
      compcert.override.version = "3.17";
      wasmcert.job = false;
      wasmcert.override.version = "v2.2.0";
      ExtLib.job = false;
      ExtLib.override.version = "0.13.0";
      metarocq.job = true;
      metarocq.override.version = "9.1";
    }; rocqPackages = {
      rocq-core.override.version = "9.1";
    };
  };

  bundles."default".push-branches = ["master"];

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = { };
  cachix.math-comp = { };
  cachix.coq-community = { };
  cachix.metarocq = {};

  cachix.metarocq.authToken = "CACHIX_AUTH_TOKEN";

}
