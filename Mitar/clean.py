import shutil
from pathlib import Path
from Mitar.project import find_project_root


def clean(print_info: bool, start: Path | None = None):
    root = find_project_root(start or Path.cwd())
    shutil.rmtree(root / ".ProofScript", ignore_errors = True)
    shutil.rmtree(root / ".Mitar" / "build", ignore_errors = True)

    if print_info:
        print(f"\n\033[32m\033[1m✓ Mitar's auxiliary files have been cleaned up successfully\033[0m\n")


if __name__ == "__main__":
    clean(True)
