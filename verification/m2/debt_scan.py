"""Lean source lexer for the CI proof-debt gate."""
import re

FORBIDDEN = {'sorry', 'admit', 'axiom', 'sorryAx', 'unsafe', 'opaque'}

def code_only(source):
    """Mask comments/string literals, preserving positions; reject ambiguous inputs.

    Interpolated strings and character/quotation syntax are rejected for manual
    inspection instead of risking masking Lean expressions. This exact candidate
    has none. Kernel axiom checks and ZIP integrity are separate mandatory gates.
    """
    output = list(source)
    i, n = 0, len(source)

    def mask(start, end):
        for j in range(start, end):
            if output[j] not in '\r\n':
                output[j] = ' '

    while i < n:
        start = i
        if source.startswith('--', i):
            end = source.find('\n', i)
            i = n if end < 0 else end
            mask(start, i)
        elif source.startswith('/-', i):
            depth, i = 1, i + 2
            while i < n and depth:
                if source.startswith('/-', i):
                    depth, i = depth + 1, i + 2
                elif source.startswith('-/', i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise ValueError('Unterminated block comment')
            mask(start, i)
        elif source.startswith("''", i):
            # Lean's set-image notation is code, not a character literal.
            i += 2
        elif source[i] == "'" and (i == 0 or not
                (source[i - 1].isalnum() or source[i - 1] in "_'")):
            raise ValueError('Character/quotation literal requires manual inspection')
        elif (raw := re.match(r'r(#+)"', source[i:])):
            delimiter = '"' + raw[1]
            end = source.find(delimiter, i + len(raw[0]))
            if end < 0:
                raise ValueError('Unterminated raw string')
            i = end + len(delimiter)
            mask(start, i)
        elif source[i] == '"':
            if source[:i].rstrip().endswith('!'):
                raise ValueError('Interpolated/macro string requires manual inspection')
            i += 1
            while i < n and source[i] != '"':
                i += 2 if source[i] == '\\' else 1
            if i >= n:
                raise ValueError('Unterminated string')
            i += 1
            mask(start, i)
        else:
            i += 1
    return ''.join(output)

def forbidden_tokens(source):
    return [m.group() for m in re.finditer(r"[^\W\d][\w']*", code_only(source))
            if m.group() in FORBIDDEN]
