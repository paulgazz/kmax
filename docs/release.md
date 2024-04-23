<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Release process](#release-process)
  - [Versioning](#versioning)
  - [Release candidates](#release-candidates)
  - [Steps](#steps)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Release process

## Versioning

Semantic versioning

major.minor[.patch]

Use patch for bugfixes

## Release candidates

major.minor-rcN

Use a release candidate before a major or minor release.

Single commit releases and patch releases don't need a release candidate.

## Steps

1. Bump version in kmax/about.py (perhaps this should be automated from [or to] git somehow?)
2. Add a new tag for the version in git, prefixed with a "v", e.g., v4.3.1, annotated with a description of the new version.  Use this to get a log of changes

        git log --pretty="- %s" v4.5.2..HEAD

3. Make a release on github for major, minor, and patch version changes, using the same description from above for the release.
4. Publish to pypi (see scripts/pypi.sh)
