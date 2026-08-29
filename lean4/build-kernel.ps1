$ErrorActionPreference = "Stop"
$root = Split-Path -Parent $MyInvocation.MyCommand.Path
Push-Location $root
try {
  $forbidden = rg -n --glob "*.lean" "\bsorry\b|\badmit\b|^\s*axiom\b|^\s*opaque\b|^\s*unsafe\b|native_decide|ofReduceBool|Lean\.trustCompiler"
  if ($LASTEXITCODE -eq 0) {
    $forbidden
    throw "Kernel-only source gate failed"
  }
  if ($LASTEXITCODE -ne 1) {
    throw "Kernel-only source scan failed"
  }

  lake build FibonacciRibbonKernel.CurrentKernelRoot
  if ($LASTEXITCODE -ne 0) {
    throw "Lean build failed"
  }

  python verify-formula-map.py
  if ($LASTEXITCODE -ne 0) {
    throw "Manuscript formula-map coverage failed"
  }

  Write-Output "fibonacci_ribbon_kernel=passed trust=0 custom_axioms=none labels=47"
} finally {
  Pop-Location
}
