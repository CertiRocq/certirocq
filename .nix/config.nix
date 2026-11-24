let
  ## Rocq 9.2 and the 9.2 branch of MetaRocq, shared by the bundles below.
  ## The other libraries CertiRocq depends on are the releases that nixpkgs
  ## selects for Rocq 9.2.
  rocqPackages = {
    rocq-core.override.version = "9.2";
    coq.override.version = "9.2";
    metarocq.job = false;
    metarocq.override.version = "9.2";
    metarocq-erasure-plugin.job = true;
    metarocq-safechecker-plugin.job = true;
    equations.job = false;
    ExtLib.job = false;
    compcert.job = false;
    wasmcert.job = false;
  };
in
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
  ## The default bundle uses Rocq 9.2 and the 9.2 branch of MetaRocq.
  bundles."default" = {
    inherit rocqPackages;
  };
  ## The same, with the check phase also building and testing the
  ## bootstrapped compiler and checker, which takes about 15 more minutes.
  ## It has no generated workflow: .github/workflows/nix-bootstrap.yml
  ## builds it on the pull requests labeled "bootstrap".
  bundles."bootstrap" = {
    rocqPackages = rocqPackages // {
      CertiRocq.override.bootstrap = true;
    };
  };

  bundles."default".push-branches = ["rocq-9.2"];
  ## genNixActions makes the workflow run on pull_request_target, which
  ## GitHub always takes from the default branch (main), not from the PR's
  ## base branch: PRs to rocq-9.2 would then get no Nix CI.  After
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
