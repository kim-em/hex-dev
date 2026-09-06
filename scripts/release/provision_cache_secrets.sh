#!/usr/bin/env bash
#
# Provision the Lake cache credentials on every released mirror.
#
# The mirrors publish their oleans to Hex's R2 bucket, which needs one secret
# and two variables per repository. released-ci.yml decides which repositories
# exist, so adding a repository there and re-running this is all it takes: the
# script is idempotent and only touches what is missing or wrong.
#
# The token is an R2 API token with Object Read & Write on the hex-cache bucket,
# in `curl --user` form: <ACCESS_KEY_ID>:<SECRET_ACCESS_KEY>. It is read from
# $HEX_LAKE_CACHE_KEY, or from a file (default ~/.config/hex/lake-cache-key),
# and never appears in this script's output.
#
# Usage:
#   scripts/release/provision_cache_secrets.sh            # provision
#   scripts/release/provision_cache_secrets.sh --check    # report, change nothing
#
# `--check` needs no token, so it is safe to run anywhere `gh` is authenticated.
set -euo pipefail

cd "$(dirname "$0")/../.."

KEY_FILE=${HEX_LAKE_CACHE_KEY_FILE:-$HOME/.config/hex/lake-cache-key}
SECRET_NAME=HEX_LAKE_CACHE_KEY
ACCOUNT=5acf032f740d48aa656788e28cabcf2e
BUCKET=hex-cache
# The signed S3 API host, for uploads.
ARTIFACT_ENDPOINT="https://$ACCOUNT.r2.cloudflarestorage.com/$BUCKET/artifacts"
REVISION_ENDPOINT="https://$ACCOUNT.r2.cloudflarestorage.com/$BUCKET/revisions"
# The public host, for downloads: Lake's fetcher sends no credentials, so reads
# go through the bucket's public URL rather than the S3 API. Set here so that
# teaching the mirrors to restore their own dependencies needs no second pass.
PUBLIC=https://pub-1ad7cebeb89e49d5afe6887b57e7956a.r2.dev
ARTIFACT_ENDPOINT_PUBLIC="$PUBLIC/artifacts"
REVISION_ENDPOINT_PUBLIC="$PUBLIC/revisions"

# Printed whenever the token is missing. R2 shows a secret key once and never
# again, so a lost file is not recoverable: it means minting a new token. Anyone
# who hits this, including an agent driving the script, gets the whole procedure
# here rather than having to find it.
no_token() {
  cat <<TXT
No R2 token found. Looked at \$HEX_LAKE_CACHE_KEY and $KEY_FILE.

If the file was lost, the token cannot be recovered: Cloudflare shows an R2
secret key once. Mint a new one. The old one can keep working, or be deleted
from the same screen; a bucket may have several.

  1. Cloudflare dashboard -> R2 -> Manage R2 API Tokens -> Create API token.
  2. Name it something like hex-cache-ci.
  3. Permissions: Object Read & Write. Not Admin: publishing only ever puts and
     gets objects, and never creates or deletes a bucket.
  4. Apply to specific buckets only -> $BUCKET. The default is every bucket in
     the account, which is more than this needs.
  5. Leave the TTL forever and client IP filtering empty; GitHub runners have no
     stable egress addresses.
  6. Create, then copy both the Access Key ID and the Secret Access Key.

Store it, in a normal shell rather than through an agent, so the secret does not
land in a transcript:

  mkdir -p "\$(dirname "$KEY_FILE")" && chmod 700 "\$(dirname "$KEY_FILE")"
  printf '%s' 'ACCESS_KEY_ID:SECRET_ACCESS_KEY' > $KEY_FILE
  chmod 600 $KEY_FILE

The colon-joined form is what Lake hands to \`curl --user\` (uploadS3 in
Lake/Config/Cache.lean).

Check it before provisioning 57 repositories with it. Both must print 200, and
the second must print the body 'probe':

  KEY=\$(< $KEY_FILE)
  echo probe > /tmp/probe.txt
  curl -s -o /dev/null -w 'PUT %{http_code}\\n' --aws-sigv4 aws:amz:auto:s3 \\
    --user "\$KEY" -X PUT -T /tmp/probe.txt \\
    $ARTIFACT_ENDPOINT/_probe.txt
  curl -s -w ' GET %{http_code}\\n' $ARTIFACT_ENDPOINT_PUBLIC/_probe.txt

A 403 on the PUT means the token is scoped to the wrong bucket or was created
read-only. Then re-run this script.
TXT
}

check_only=false
[[ ${1:-} == "--check" ]] && check_only=true

mapfile -t repos < <(python3 - <<'PY'
import yaml
for name in yaml.safe_load(open("scripts/release/released-ci.yml"))["workflows"]:
    print(f"leanprover/{name}")
# hex-dev publishes under its own scope from its own CI, and carries the same
# credentials so the two sides can converge on one secret name.
print("kim-em/hex-dev")
PY
)

if ! $check_only; then
  key=${HEX_LAKE_CACHE_KEY:-}
  if [[ -z "$key" && -r "$KEY_FILE" ]]; then
    key=$(< "$KEY_FILE")
  fi
  key=${key%%[$'\n\r']*}
  if [[ -z "$key" ]]; then
    no_token >&2
    exit 2
  fi
  if [[ "$key" != *:* ]]; then
    echo "The token in $KEY_FILE is not in <ACCESS_KEY_ID>:<SECRET_ACCESS_KEY> form." >&2
    echo "Lake passes it straight to \`curl --user\`, so it must be the two halves" >&2
    echo "joined by a colon, with no spaces or newline." >&2
    echo >&2
    no_token >&2
    exit 2
  fi
fi

missing=0
for repo in "${repos[@]}"; do
  have_secret=$(gh secret list --repo "$repo" --json name --jq \
    "[.[] | select(.name == \"$SECRET_NAME\")] | length" 2>/dev/null || echo 0)
  vars_json=$(gh api "repos/$repo/actions/variables" --jq \
    '[.variables[] | select(.name | startswith("HEX_LAKE_CACHE_")) | "\(.name)=\(.value)"] | sort | join(" ")' 2>/dev/null || echo "")
  want_vars="HEX_LAKE_CACHE_ARTIFACT_ENDPOINT=$ARTIFACT_ENDPOINT HEX_LAKE_CACHE_ARTIFACT_ENDPOINT_PUBLIC=$ARTIFACT_ENDPOINT_PUBLIC HEX_LAKE_CACHE_REVISION_ENDPOINT=$REVISION_ENDPOINT HEX_LAKE_CACHE_REVISION_ENDPOINT_PUBLIC=$REVISION_ENDPOINT_PUBLIC"

  if $check_only; then
    state=""
    [[ "$have_secret" == 1 ]] || state+=" secret"
    [[ "$vars_json" == "$want_vars" ]] || state+=" variables"
    if [[ -n "$state" ]]; then
      echo "MISSING$state  $repo"
      missing=1
    fi
    continue
  fi

  changed=""
  if [[ "$vars_json" != "$want_vars" ]]; then
    gh variable set HEX_LAKE_CACHE_ARTIFACT_ENDPOINT --repo "$repo" --body "$ARTIFACT_ENDPOINT" >/dev/null
    gh variable set HEX_LAKE_CACHE_REVISION_ENDPOINT --repo "$repo" --body "$REVISION_ENDPOINT" >/dev/null
    gh variable set HEX_LAKE_CACHE_ARTIFACT_ENDPOINT_PUBLIC --repo "$repo" --body "$ARTIFACT_ENDPOINT_PUBLIC" >/dev/null
    gh variable set HEX_LAKE_CACHE_REVISION_ENDPOINT_PUBLIC --repo "$repo" --body "$REVISION_ENDPOINT_PUBLIC" >/dev/null
    changed+=" variables"
  fi
  if [[ "$have_secret" != 1 ]]; then
    printf '%s' "$key" | gh secret set "$SECRET_NAME" --repo "$repo" >/dev/null
    changed+=" secret"
  fi
  if [[ -n "$changed" ]]; then
    printf 'set%-22s %s\n' "$changed" "$repo"
  else
    printf '%-25s %s\n' "already provisioned" "$repo"
  fi
done

if $check_only && (( missing )); then
  echo
  echo "run scripts/release/provision_cache_secrets.sh to fix" >&2
  exit 1
fi
