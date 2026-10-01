# Changelog

<!-- changelog:unreleased -->
## [Unreleased]

### Features
- Add a scratch probe used to exercise the changelog automation. ([#1283](../../pull/1283))
- Add an API for compact UUID-to-string conversion. ([#9004](../../pull/9004))

### Fixes
- Stop leaking the allocator when a probe fails to initialise. ([#9002](../../pull/9002))

### Notes
- [#9004](../../pull/9004) — Callers that relied on the dashed form keep working; the compact form is opt-in.
<!-- /changelog:unreleased -->

## [1.0.0]

Official release of 1.0.0.
