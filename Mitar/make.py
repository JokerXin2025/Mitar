import sys, json, subprocess
from pathlib import Path
from Mitar.Rules import Initialize
from Mitar.engine import ProofEngine
from Mitar.Lean2TeX import Lean2TeX_init


def make(input_path: str):

    Initialize()
    input_file = Path(input_path)
    json_file = input_file.with_name(f"{input_file.stem}_Lean2TeX.json")
    output_file = input_file.with_suffix(".html")

    Lean2TeX_init_ = Lean2TeX_init(input_file)

    if Lean2TeX_init_ == 1:
        # Error: Configuration file not found
        print(f"\n\033[31m\033[1m✗ Configuration file not found\033[0m\n")
        return
    elif Lean2TeX_init_ == 2:
        # Error: Input file not found
        print(f"\n\033[31m\033[1m✗ File \033[4m{input_file}\033[0m\033[31m\033[1m not found\033[0m\n")
        return

    result = subprocess.run(
        ["lake", "build"],
        cwd = Path.cwd(),
        text = True,
        capture_output = True
    )

    if result.returncode:
        # Error: Lean4 build failure
        print(f"\n\033[31m\033[1m✗ Lean4 failed to build \033[4m{input_file}\033[0m\n")
        return

    if json_file.exists():
        with open(json_file, 'r', encoding = 'utf-8') as f:
            data = json.load(f)
    else:
        # Error: Lean2TeX internal error
        print(f"\n\033[31m\033[1m✗ Some internal error from Lean2TeX occurred\033[0m\n")
        return

    output_file.write_text(ProofEngine(data).make(), encoding = "utf-8")
    print(f"\n\033[32m\033[1m✓ Output file has been saved to \033[4m{output_file}\033[0m\n")


if __name__ == "__main__":

    make(sys.argv[1])
