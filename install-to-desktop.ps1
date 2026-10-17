$ErrorActionPreference = 'Stop'
$source = $PSScriptRoot
$desktop = [Environment]::GetFolderPath('Desktop')
if ([string]::IsNullOrWhiteSpace($desktop)) { throw 'Windows Desktop folder was not found.' }
$destination = Join-Path $desktop 'logical_midterm'
if ([IO.Path]::GetFullPath($source).TrimEnd('\') -eq [IO.Path]::GetFullPath($destination).TrimEnd('\')) {
    Start-Process explorer.exe -ArgumentList ('"' + $destination + '"')
    exit 0
}
if (Test-Path -LiteralPath $destination) {
    $destination = Join-Path $desktop ('logical_midterm-' + (Get-Date -Format 'yyyyMMdd-HHmmss') + '-' + [Guid]::NewGuid().ToString('N').Substring(0,6))
}
Copy-Item -LiteralPath $source -Destination $destination -Recurse -ErrorAction Stop
Write-Host ('Project copied to: ' + $destination)
Start-Process explorer.exe -ArgumentList ('"' + $destination + '"')
