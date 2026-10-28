// Compute the reachability closure of the TrotterError headline targets from the
// Stage-1 declaration graph, and apply the Phase-2 classification rules.
// Usage: pwsh -File reach.ps1
$ErrorActionPreference = 'Stop'

$graphPath = 'D:\project\CQM1\decl_graph.jsonl'
$outPath   = 'D:\project\CQM1\tools\p2m\reachability.json'

# ---- load graph (UTF-8, explicit) -------------------------------------------
$txt   = [System.IO.File]::ReadAllText($graphPath, [System.Text.Encoding]::UTF8)
$lines = $txt -split "`n" | Where-Object { $_.Trim() -ne '' }

$byName = @{}
foreach ($l in $lines) {
    $r = $l | ConvertFrom-Json
    $byName[$r.name] = $r
}
Write-Host "graph declarations: $($byName.Count)"

# ---- roots: the TrotterError targets ----------------------------------------
$roots = @(
    'TrotterError.trotter_error_bound_comm_scaling'
    'TrotterError.trotter_error_comm_scaling'
    'TrotterError.trotter_error_bound_comm_scaling_of_skewAdjoint'
    'TrotterError.trotter_error_comm_scaling_of_skewAdjoint'
    'TrotterError.multiplicative_error_bound_comm_scaling'
    'TrotterError.multiplicative_error_comm_scaling'
    'TrotterError.multiplicative_error_bound_comm_scaling_of_skewAdjoint'
    'TrotterError.multiplicative_error_comm_scaling_of_skewAdjoint'
    'TrotterError.trotter_error_bound_one_norm_scaling'
    'TrotterError.trotter_error_one_norm_scaling'
    'TrotterError.trotter_number_one_norm_scaling'
)

# ---- BFS over typeDeps + valueDeps ------------------------------------------
# Roots are given by user-facing userName; the graph keys on the internal name
# (private decls are `_private.<mod>.<n>.<userName>`), so index by userName too.
$byUser = @{}
foreach ($k in $byName.Keys) { $byUser[$byName[$k].userName] = $byName[$k] }

$visited = New-Object 'System.Collections.Generic.HashSet[string]'
$queue   = New-Object 'System.Collections.Generic.Queue[string]'
foreach ($t in $roots) {
    if (-not $byUser.ContainsKey($t)) { Write-Warning "root not found: $t"; continue }
    [void]$queue.Enqueue($byUser[$t].name)
}
while ($queue.Count -gt 0) {
    $cur = $queue.Dequeue()
    if (-not $visited.Add($cur)) { continue }
    if (-not $byName.ContainsKey($cur)) { continue }
    $row = $byName[$cur]
    foreach ($d in @($row.typeDeps) + @($row.valueDeps)) {
        if ($byName.ContainsKey($d)) { [void]$queue.Enqueue($d) }
    }
}

# ---- drop spanless rows AFTER reachability (playbook rule) ------------------
$reached = $visited | ForEach-Object { $byName[$_] }
$kept    = $reached | Where-Object { $_.startLine -gt 0 }

Write-Host ""
Write-Host "=== reachability ==="
Write-Host "reached (incl. compiler-generated): $($reached.Count)"
Write-Host "kept (real source spans):           $($kept.Count)"
Write-Host "dropped as spanless:                $($reached.Count - $kept.Count)"

Write-Host ""
Write-Host "=== kept, by module ==="
$kept | Group-Object module | Sort-Object Name |
    ForEach-Object { "  {0,-45} {1,4}" -f $_.Name, $_.Count }

Write-Host ""
Write-Host "=== kept, by kind ==="
$kept | Group-Object kind | Sort-Object Count -Descending |
    ForEach-Object { "  {0,-12} {1,4}" -f $_.Name, $_.Count }

# ---- how much of the original tree survives --------------------------------
$teAll = $byName.Values | Where-Object { $_.module -like 'FQFP.TrotterError*' -and $_.startLine -gt 0 }
Write-Host ""
Write-Host "=== dead code within TrotterError ==="
Write-Host "  TrotterError decls with spans: $($teAll.Count)"
Write-Host "  of those, reachable & kept:    $(($kept | Where-Object { $_.module -like 'FQFP.TrotterError*' }).Count)"

# ---- leakage check: does the closure leave TrotterError? -------------------
$outside = $kept | Where-Object { $_.module -notlike 'FQFP.TrotterError*' }
Write-Host ""
Write-Host "=== closure leakage outside TrotterError: $($outside.Count) ==="
$outside | Group-Object module | ForEach-Object { "  {0,-45} {1,4}" -f $_.Name, $_.Count }

# ---- persist ---------------------------------------------------------------
$result = [ordered]@{
    roots   = $roots
    reached = $reached.Count
    kept    = $kept.Count
    keptByModule = @{}
    outside = @($outside | ForEach-Object { $_.name })
    keptNames = @($kept | ForEach-Object { $_.name })
}
foreach ($g in ($kept | Group-Object module)) { $result.keptByModule[$g.Name] = $g.Count }
$json = $result | ConvertTo-Json -Depth 6
[System.IO.File]::WriteAllText($outPath, $json, (New-Object System.Text.UTF8Encoding $false))
Write-Host ""
Write-Host "wrote $outPath"
