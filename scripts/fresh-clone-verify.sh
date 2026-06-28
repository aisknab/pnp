#!/usr/bin/env bash
set -Eeuo pipefail

COORDINATE="PNP-FRESH-CLONE-VERIFY-2026-06-27-01"
DEFAULT_INSTALL_COMMAND="npm ci"
DEFAULT_VERIFY_COMMAND="npm run pnp:verify"
DEFAULT_VERDICT_PATH="artifacts/fresh-clone-verify/latest-verdict.json"

repo=""
ref=""
workdir=""
install_command="$DEFAULT_INSTALL_COMMAND"
verify_command="$DEFAULT_VERIFY_COMMAND"
verdict_path="$DEFAULT_VERDICT_PATH"
keep_workdir="false"
current_phase="start"
clone_dir=""
created_temp_workdir="false"

usage() {
  cat <<'USAGE'
Usage: bash scripts/fresh-clone-verify.sh [options]

Options:
  --repo <url-or-path>          Repository URL or local path. Defaults to git remote.origin.url.
  --ref <ref-or-sha>            Ref, branch, tag, or commit SHA. Defaults to current HEAD.
  --workdir <path>              Work directory. Defaults to a temporary directory.
  --install-command <command>   Install command. Defaults to: npm ci
  --verify-command <command>    Verify command. Defaults to: npm run pnp:verify
  --verdict <path>              Verdict JSON path. Defaults to artifacts/fresh-clone-verify/latest-verdict.json.
  --keep-workdir                Do not remove the work directory on exit.
  -h, --help                    Print help.
USAGE
}

json_escape() {
  node -e 'process.stdout.write(JSON.stringify(process.argv[1] ?? ""))' "$1"
}

write_verdict() {
  local tag="$1"
  local phase="$2"
  local exit_code="$3"
  local output_dir
  output_dir="$(dirname "$verdict_path")"
  mkdir -p "$output_dir"
  cat > "$verdict_path" <<JSON
{
  "tag": $(json_escape "$tag"),
  "kind": $(json_escape "$tag"),
  "coordinate": $(json_escape "$COORDINATE"),
  "checker": "FreshCloneVerifyScript0",
  "version": 0,
  "phase": $(json_escape "$phase"),
  "exitCode": $exit_code,
  "repo": $(json_escape "$repo"),
  "ref": $(json_escape "$ref"),
  "workdir": $(json_escape "$workdir"),
  "cloneDir": $(json_escape "$clone_dir"),
  "installCommand": $(json_escape "$install_command"),
  "verifyCommand": $(json_escape "$verify_command"),
  "freshCloneVerifierReady": true,
  "publicTheoremEmissionAllowed": false,
  "finalTheoremReady": false,
  "activeFinalNodeIds": [],
  "remainingBlockers": [
    "Release.UnrestrictedFinalSoundness",
    "ExternalReview.Acceptance"
  ]
}
JSON
}

cleanup() {
  local code=$?
  if [[ "$keep_workdir" != "true" && "$created_temp_workdir" == "true" && -n "$workdir" && -d "$workdir" ]]; then
    rm -rf "$workdir"
  fi
  return "$code"
}

on_error() {
  local code=$?
  write_verdict "reject" "$current_phase" "$code" || true
  exit "$code"
}

trap cleanup EXIT
trap on_error ERR

while [[ $# -gt 0 ]]; do
  case "$1" in
    --repo)
      repo="${2:?--repo requires a value}"
      shift 2
      ;;
    --ref)
      ref="${2:?--ref requires a value}"
      shift 2
      ;;
    --workdir)
      workdir="${2:?--workdir requires a value}"
      shift 2
      ;;
    --install-command)
      install_command="${2:?--install-command requires a value}"
      shift 2
      ;;
    --verify-command)
      verify_command="${2:?--verify-command requires a value}"
      shift 2
      ;;
    --verdict)
      verdict_path="${2:?--verdict requires a value}"
      shift 2
      ;;
    --keep-workdir)
      keep_workdir="true"
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

current_phase="resolve-repo"
if [[ -z "$repo" ]]; then
  repo="$(git config --get remote.origin.url)"
fi
if [[ -z "$repo" ]]; then
  echo "could not determine repository; pass --repo" >&2
  exit 2
fi

current_phase="resolve-ref"
if [[ -z "$ref" ]]; then
  ref="$(git rev-parse HEAD)"
fi
if [[ -z "$ref" ]]; then
  echo "could not determine ref; pass --ref" >&2
  exit 2
fi

current_phase="prepare-workdir"
if [[ -z "$workdir" ]]; then
  workdir="$(mktemp -d "${TMPDIR:-/tmp}/pnp-fresh-clone.XXXXXX")"
  created_temp_workdir="true"
else
  mkdir -p "$workdir"
fi
clone_dir="$workdir/repo"
rm -rf "$clone_dir"

current_phase="git-clone"
git clone --no-tags "$repo" "$clone_dir"

current_phase="git-checkout"
if git -C "$clone_dir" rev-parse --verify --quiet "${ref}^{commit}" >/dev/null; then
  git -C "$clone_dir" checkout --detach "$ref"
else
  git -C "$clone_dir" fetch --no-tags --depth 1 origin "$ref"
  git -C "$clone_dir" checkout --detach FETCH_HEAD
fi

current_phase="install"
(
  cd "$clone_dir"
  eval "$install_command"
)

current_phase="verify"
(
  cd "$clone_dir"
  eval "$verify_command"
)

current_phase="complete"
write_verdict "accept" "$current_phase" 0
