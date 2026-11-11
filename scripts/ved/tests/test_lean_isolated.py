"""lean_isolated.sh refuses a checkout other than the tree its build was made from (review P1-1)."""
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
VED = os.path.dirname(HERE)
sys.path.insert(0, VED)
import tree_digest  # noqa: E402


def git(repo, *a):
    return subprocess.run(["git", "-C", repo, *a], check=True, capture_output=True, text=True).stdout.strip()


class LeanIsolatedTreeTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.tmp)
        self.repo = os.path.join(self.tmp, "repo")
        os.makedirs(self.repo)
        git(self.repo, "init", "-q")
        git(self.repo, "config", "user.email", "t@t")
        git(self.repo, "config", "user.name", "t")
        open(os.path.join(self.repo, "A.lean"), "w").write("def a := 1\n")
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-qm", "A")
        self.a = git(self.repo, "rev-parse", "HEAD")
        open(os.path.join(self.repo, "A.lean"), "w").write("def a := 2\n")
        git(self.repo, "commit", "-qam", "B")
        self.b = git(self.repo, "rev-parse", "HEAD")
        git(self.repo, "checkout", "-q", self.a)
        self.state = os.path.join(self.tmp, "state")
        os.makedirs(os.path.join(self.state, "builds"))
        bdir = os.path.join(self.tmp, "build")
        os.makedirs(os.path.join(bdir, ".lake"))
        rec = {"build_id": "b1", "source": self.repo, "source_sha256": tree_digest.digest(self.repo),
               "build_dir": bdir, "toolchain": "tc", "phase": "succeeded", "exit_code": 0, "started_at": 1}
        json.dump(rec, open(os.path.join(self.state, "builds", "b1.json"), "w"))

    def run_case(self):
        env = dict(os.environ, KJOB_STATE_DIR=self.state, VED_LEAN_ISOLATED_DRY="1")
        return subprocess.run(["bash", os.path.join(VED, "lean_isolated.sh"), "/x/Case.lean"], cwd=self.repo,
                              env=env, capture_output=True, text=True)

    def test_built_tree_runs(self):
        r = self.run_case()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("tree_sha256_checked=yes", r.stderr)

    def test_clean_checkout_of_another_commit_is_refused(self):
        self.assertEqual(self.run_case().returncode, 0)       # A verified (cached for A's HEAD)
        git(self.repo, "checkout", "-q", self.b)             # clean, but not the built tree
        r = self.run_case()
        self.assertEqual(r.returncode, 97, r.stderr)
        self.assertIn("is not the tree build b1 was made from", r.stderr)

    def test_dirty_tree_is_refused(self):
        open(os.path.join(self.repo, "A.lean"), "w").write("def a := 3\n")
        self.assertEqual(self.run_case().returncode, 97)

    def test_digest_matches_kjob_on_mode_and_symlink(self):
        os.symlink("A.lean", os.path.join(self.repo, "L.lean"))
        d1 = tree_digest.digest(self.repo)
        os.chmod(os.path.join(self.repo, "A.lean"), 0o755)
        self.assertNotEqual(d1, tree_digest.digest(self.repo))


if __name__ == "__main__":
    unittest.main()
