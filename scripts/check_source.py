"""Conservative source hygiene and project-import checks (not a Lean parser)."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def code_only(text):
    # Blank nested comments and string literals while retaining line numbers.
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair, char = text[i:i + 2], text[i]
        if depth:
            if pair == '/-':
                depth += 1; out.extend('  '); i += 2; continue
            if pair == '-/':
                depth -= 1; out.extend('  '); i += 2; continue
            out.append('\n' if char == '\n' else ' ')
        elif string:
            if char == '\\' and i + 1 < len(text):
                out.extend('  '); i += 2; continue
            if char == '"': string = False
            out.append('\n' if char == '\n' else ' ')
        elif pair == '/-':
            depth = 1; out.extend('  '); i += 2; continue
        elif pair == '--':
            end = text.find('\n', i)
            if end < 0: end = len(text)
            out.extend(' ' * (end - i)); i = end; continue
        elif char == '"':
            string = True; out.append(' ')
        else:
            out.append(char)
        i += 1
    if depth or string:
        raise ValueError('Unclosed comment or string')
    return ''.join(out)


def main():
    files = [ROOT / 'MagicSquares.lean', *sorted((ROOT / 'MagicSquares').rglob('*.lean'))]
    graph, errors = {}, []
    for path in files:
        module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
        code = code_only(path.read_text(encoding='utf-8'))
        for match in re.finditer(r'\b(sorry|admit|axiom|native_decide|implemented_by|unsafe)\b', code):
            line = code.count('\n', 0, match.start()) + 1
            errors.append(f'{path.relative_to(ROOT)}:{line}: review forbidden token {match[0]}')
        imports = []
        for line in re.findall(r'^\s*import\s+([^\n]+)', code, re.M):
            imports.extend(x for x in line.split() if x == 'MagicSquares' or x.startswith('MagicSquares.'))
        graph[module] = imports
    visiting, visited = set(), set()
    def visit(module):
        if module not in graph:
            errors.append(f'Missing project import: {module}'); return
        if module in visiting:
            errors.append(f'Import cycle: {module}'); return
        if module in visited: return
        visiting.add(module)
        for dependency in graph[module]: visit(dependency)
        visiting.remove(module); visited.add(module)
    for module in graph: visit(module)
    if errors:
        raise SystemExit('\n'.join(errors))
    print(f'PASS: {len(files)} project sources; no flagged code tokens, missing project imports, or import cycles.')
    print('This static check does not establish the compiled endpoint axioms.')


if __name__ == '__main__':
    main()
