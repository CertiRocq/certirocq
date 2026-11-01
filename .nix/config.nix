{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/rocq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "CertiRocq";

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  # pname = "{{shortname}}";

  default-bundle = "default";
  ## When generating GitHub Action CI, one workflow file
  ## will be created per bundle
  ## The default bundle uses the development branches of Rocq
  ## and of all the libraries CertiRocq depends on.
  bundles."default" = {
    rocqPackages = {
      rocq-core.override.version = "master";
      coq.override.version = "master";
      stdlib.override.version = "master";
      metarocq.job = false;
      metarocq.override.version = "main";
      metarocq-erasure.job = true;
      metarocq-safechecker.job = true;
      equations.job = false;
      equations.override.version = "main";
      ExtLib.job = false;
      ExtLib.override.version = "master";
      compcert.job = false;
      compcert.override.version = "master";
      MenhirLib.job = false;
      MenhirLib.override.version = "master";
      flocq.job = false;
      flocq.override.version = "master";
      wasmcert.job = false;
      wasmcert.override.version = "rocq-master";
      mathcomp.job = false;
      mathcomp.override.version = "master";
      parseque.job = false;
      parseque.override.version = "master";
      hierarchy-builder.job = false;
      hierarchy-builder.override.version = "master";
      rocq-elpi.job = false;
      rocq-elpi.override.version = "master";
    };
  };

  bundles."default".push-branches = ["rocq-master"];
  ## genNixActions makes the workflow run on pull_request_target, which
  ## GitHub always takes from the default branch (main), not from the PR's
  ## base branch: PRs to rocq-master would then get no Nix CI.  After
  ## regenerating .github/workflows/nix-action-default.yml, replace its
  ## pull_request and pull_request_target triggers by a plain, unfiltered
  ## pull_request one (fork PRs then cannot push to the cache, but are built).

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = { };
  cachix.math-comp = { };
  cachix.coq-community = { };
  cachix.metarocq = {};

  cachix.metarocq.authToken = "CACHIX_AUTH_TOKEN";

}
