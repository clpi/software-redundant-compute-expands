"""Append-only replica and watermark control. No transport or signing backend."""
from dataclasses import dataclass
from hashlib import sha256
import json


def identity(source, sequence, parent, payload):
    body = json.dumps([source, sequence, parent, payload], ensure_ascii=True,
                      separators=(",", ":"), sort_keys=True)
    return sha256(body.encode()).hexdigest()


@dataclass(frozen=True)
class Event:
    source: str
    sequence: int
    parent: str
    payload: str

    @property
    def digest(self):
        return identity(self.source, self.sequence, self.parent, self.payload)


@dataclass(frozen=True)
class Watermark:
    source: str
    sequence: int
    digest: str

    # Trust boundary: callers only insert marks authenticated by the source.


@dataclass(frozen=True)
class Replica:
    events: frozenset = frozenset()
    marks: frozenset = frozenset()

    def join(self, other):
        return Replica(self.events | other.events, self.marks | other.marks)

    def receipt(self, source, required_through):
        marks = {}
        for m in self.marks:
            if m.source == source:
                marks.setdefault(m.sequence, set()).add(m.digest)
        # Checkpoint freshness is a policy argument. No heartbeat can prove
        # absence of unknown writes after the most recent trusted boundary.
        frontier = max(marks, default=-1)
        if frontier < required_through:
            return ("stale" if marks else "unsupported", frontier)
        if any(len(v) != 1 for v in marks.values()):
            return ("conflict", frontier)
        index = {}
        for e in self.events:
            if e.source == source and e.sequence <= frontier:
                index.setdefault(e.sequence, set()).add(e)
        if any(len(v) != 1 for v in index.values()):
            return ("conflict", frontier)
        missing = tuple(i for i in range(frontier + 1) if i not in index)
        if missing:
            return ("missing", missing)
        parent = ""
        for i in range(frontier + 1):
            e = next(iter(index[i]))
            if e.parent != parent:
                return ("conflict", frontier)
            parent = e.digest
            if i in marks and parent not in marks[i]:
                return ("conflict", frontier)
        return ("complete-through", frontier)


def lane(source, texts):
    parent, events, marks = "", [], []
    for i, payload in enumerate(texts):
        event = Event(source, i, parent, payload)
        events.append(event)
        parent = event.digest
        marks.append(Watermark(source, i, parent))
    return events, marks
