from pathlib import Path
import re

DESCRIPTION_TEMPLATE = """\
You have to write {cnt} {functions} in dafny, using the given helper functions
The {descriptions} as follows:
"""

SUBTASK_TEMPLATE = """\
function `{name}`: {task}
"""

NO_EXAMPLES = {
    "010": ["is_palindrome"],
    "041": ["car_race_collision"],
    "050": ["encode_shift", "decode_shift"],
    "083": ["starts_one_ends"],
}

POSSIBLE_ENDS = [
    ">>>",
    "Examples",
    "for example",
    "For example",
    "Example",
    "example",
    # "\"\"\""
]


def description_from_match(number: str, name: str, task: str) -> str:
    if number in NO_EXAMPLES and name in NO_EXAMPLES[number]:
        end = len(task)
    else:
        end, pos = -1, 0
        POSSIBLE_ENDS.append(name)
        while end == -1:
            end = task.find(POSSIBLE_ENDS[pos])
            pos += 1
        POSSIBLE_ENDS.pop()
    task = task[:end].replace("    ", "").replace("\n", " ").strip()
    while "  " in task:
        task = task.replace("  ", " ")
    return SUBTASK_TEMPLATE.format(name=name, task=task)


assert (
    Path(".").absolute().stem == "HumanEval-Dafny"
), "script should be run from HumanEval-Dafny directory"

human_eval = Path(".").absolute().parent / "verified-cogen" / "benches" / "HumanEval"
text_descriptions = Path() / "text-descriptions"
text_descriptions.mkdir(exist_ok=True)

desc_regex = re.compile(r"def ([a-zA-Z0-9_]*)\(.*\)(:?\s*->\s*.*)?:\n")

files = sorted(Path(".").glob("*.dfy"))
for i, file in enumerate(files):
    number = file.stem[:3]
    name = file.stem[4:].replace("-", "_")

    prompt_path = human_eval / f"{number}_{name}/{name}.prompt"
    print(f"Done {i + 1}/{len(files)} ({prompt_path.name})")
    prompt = prompt_path.read_text()

    matches = list(desc_regex.finditer(prompt))
    desc = DESCRIPTION_TEMPLATE.format(
        cnt=len(matches),
        functions="function" if len(matches) == 1 else "functions",
        descriptions="description is" if len(matches) == 1 else "descriptions are",
    )
    for match in matches:
        desc_start = prompt.find('"""', match.end())
        if desc_start == -1:
            desc_start = prompt.find("'''", match.end())
            desc_end = prompt.find("'''", desc_start + 3)
        else:
            desc_end = prompt.find('"""', desc_start + 3)
        desc += description_from_match(
            number, match.groups()[0], prompt[desc_start + 3 : desc_end]
        )  # type: ignore

    with (text_descriptions / f"{file.stem}.txt").open("w") as out:
        out.write(desc)
