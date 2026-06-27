from pathlib import Path


def clean(print_info: bool):

    for aux_file in Path.cwd().rglob("*_Lean2TeX.lean"):
        aux_file.unlink(missing_ok = True)

    for aux_file in Path.cwd().rglob("*_Lean2TeX.json"):
        aux_file.unlink(missing_ok = True)

    if print_info:
        print(f"\n\033[32m\033[1m✓ Mitar's auxiliary files have been cleaned up successfully\033[0m\n")


if __name__ == "__main__":

    clean()
