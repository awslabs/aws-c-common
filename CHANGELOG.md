# Changelog

<!-- changelog:unreleased -->
## [Unreleased]

### Features
- Add a second scratch probe for the changelog automation. ([#1284](../../pull/1284))
- First of two entries landing in one push. ([#9010](../../pull/9010))
<!-- /changelog:unreleased -->

## [1.1.0] — 2026-10-02

### Possible Breaking Changes
- Change the probe handle to an opaque struct. ([#9006](../../pull/9006))

### Fixes
- Handle a zero-length input in the probe without asserting. ([#9007](../../pull/9007))

### Notes
- [#9006](../../pull/9006) — Code that reached into the handle's fields must use the accessors instead.

## Earlier releases

- [1.0.x](.changes/1.0.x.md)
