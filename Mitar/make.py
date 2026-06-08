import sys, json, subprocess
from pathlib import Path
from .Rules import Initialize
from .engine import ProofEngine
from .Lean2TeX import Lean2TeX_init


def make(src_filename: str):

    Initialize()
    input_file = Path.cwd() / src_filename
    json_file = input_file.with_suffix(".json")
    output_file = input_file.with_suffix(".html")

    Lean2TeX_init(input_file)
    result = subprocess.run(
        ["lake", "build"],
        cwd = Path.cwd(),
        text = True,
        capture_output = True
    )
    print(result.stderr if result.returncode else result.stdout, end = "")

    try:
        with open(json_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
    except FileNotFoundError:
        print(f"Error: File '{json_file}' not found!")
        return

    output_file.write_text(
        ProofEngine(data).make(),
        encoding = "utf-8"
    )
    print(f"Output file saved to: {output_file}")


if __name__ == "__main__":

    make(sys.argv[1], sys.argv[2])
