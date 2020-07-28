#!/usr/bin/env python3

import collections
import re
import requests
import subprocess
import os

Finding = collections.namedtuple("Finding", ["line", "text"])

def checkable_file(fn):
    if any(fn.endswith(ext) for ext in ['.h', '.cpp']):
        return '_template.' not in fn
    return False

def get_commit_files(sha):
    cmd = ['git', 'diff-tree', '--no-commit-id', '--name-only', '-r', sha]
    files = subprocess.check_output(cmd).decode().splitlines()
    return [fn for fn in files if checkable_file(fn)]

def parse_clang_output(output):
    error_re = ".*:(\d+):\d+: (.*)"
    out = []
    for l in output.splitlines():
        m = re.match(error_re, l)
        if m:
            line = int(m.group(1))
            msg = m.group(2)
            out.append(Finding(line=line, text=msg))

    return out

def get_findings(files):
    result = {}
    for fn in files:
        cmd = ['clang-tidy', '-p', 'build', fn]
        proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        out, err = proc.communicate()
        result[fn] = parse_clang_output(out.decode())
    return result

def report_github_status(repo, token, sha, findings):
    url = "https://api.github.com/repos/{}/check-runs".format(repo)
    annotations = []
    for path, findings in findings.items():
        for f in findings:
            annotations.append({
                'path': path,
                'annotation_level': 'warning',
                'start_line': f.line,
                'end_line': f.line,
                'message': f.text
            })

    data = {
        'name': 'clang-tidy',
        'head_sha': sha,
        'status': 'completed',
        'conclusion': 'neutral',
        'output': {
            'title': 'clang-tidy',
            'summary': 'Found {} items'.format(len(annotations)),
            'annotations': annotations
        }
    }

    headers = {
        'Content-Type': 'application/json',
        'Accept': 'application/vnd.github.antiope-preview+json',
        'Authorization': 'Bearer {}'.format(token),
    }

    r = requests.post(url, json=data, headers=headers)
    print(r)
    print(r.text)


def main():
    sha = os.environ['GITHUB_BASE_REF']
    files = get_commit_files(sha)
    findings = get_findings(files)

    if 'GITHUB_TOKEN' in os.environ:
        repo = os.environ['GITHUB_REPOSITORY']
        sha = os.environ['GITHUB_SHA']
        token = os.environ['GITHUB_TOKEN']
        report_github_status(repo, token, sha, findings)


if __name__ == '__main__':
    main()
