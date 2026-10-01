# Changelog

<!-- changelog:unreleased -->
## [Unreleased]

### Features
- Change the probe handle to an opaque struct. ([#9006](../../pull/9006))

### Fixes
- Handle a zero-length input in the probe without asserting. ([#9007](../../pull/9007))

### Notes
- [#9006](../../pull/9006) — Code that reached into the handle's fields must use the accessors instead.
<!-- /changelog:unreleased -->

## [1.0.2] — 2026-10-01

### Features
- Add a scratch probe used to exercise the changelog automation. ([#1283](../../pull/1283))
- Add an API for compact UUID-to-string conversion. ([#9004](../../pull/9004))

### Fixes
- Stop leaking the allocator when a probe fails to initialise. ([#9002](../../pull/9002))

### Reverts
- Revert the change that made the probe allocate on every call. ([#9005](../../pull/9005))

### Notes
- [#9004](../../pull/9004) — Callers that relied on the dashed form keep working; the compact form is opt-in.
- [#9005](../../pull/9005) — The allocation showed up on a hot path and the win it bought was not measurable.

## [1.0.0]

Official release of 1.0.0.
