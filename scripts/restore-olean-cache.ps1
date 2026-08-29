param(
  [Parameter(Mandatory = $true)]
  [string]$Archive,
  [Parameter(Mandatory = $true)]
  [string]$Manifest
)

$ErrorActionPreference = "Stop"
$repoRoot = Split-Path -Parent $PSScriptRoot
$archivePath = (Resolve-Path -LiteralPath $Archive).Path
$manifestPath = (Resolve-Path -LiteralPath $Manifest).Path
$metadata = Get-Content -Raw -LiteralPath $manifestPath | ConvertFrom-Json
$archiveHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $archivePath).Hash.ToLowerInvariant()

if ($archiveHash -ne $metadata.archive.sha256) {
  throw "Archive SHA-256 mismatch"
}

$destination = Join-Path $repoRoot "lean4\b\lib\lean"
New-Item -ItemType Directory -Force -Path $destination | Out-Null
Expand-Archive -LiteralPath $archivePath -DestinationPath $destination -Force

foreach ($entry in $metadata.files) {
  $sourcePath = Join-Path $repoRoot ($entry.source_path -replace '/', '\')
  if (-not (Test-Path -LiteralPath $sourcePath -PathType Leaf)) {
    throw "Missing bound source file: $($entry.source_path)"
  }
  $sourceHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $sourcePath).Hash.ToLowerInvariant()
  if ($sourceHash -ne $entry.source_sha256) {
    throw "Source SHA-256 mismatch: $($entry.source_path)"
  }

  $path = Join-Path $repoRoot ($entry.cache_path -replace '/', '\')
  if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
    throw "Missing restored cache file: $($entry.cache_path)"
  }
  $hash = (Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash.ToLowerInvariant()
  if ($hash -ne $entry.cache_sha256) {
    throw "Restored cache SHA-256 mismatch: $($entry.cache_path)"
  }
  if ((Get-Item -LiteralPath $path).Length -ne [int64]$entry.cache_bytes) {
    throw "Restored cache size mismatch: $($entry.cache_path)"
  }
}

Write-Output "olean_cache=verified files=$($metadata.files.Count)"
