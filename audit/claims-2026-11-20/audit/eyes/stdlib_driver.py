#!/usr/bin/env python3
"""Same-work baseline for the idol-eyes browser campaign (audit, test-only).

Does what the Idol page engine does on the script-free tasks: fetch HTML
over HTTP, parse it, resolve targets by label/role/name, fill and submit
forms, follow links, read text. No browser, no layout, no script.
Python standard library only. Reads the same tab-separated plan the Idol
driver reads on stdin and prints 'answer\t<text>' as its last line.
"""
import sys, urllib.request, urllib.parse
from html.parser import HTMLParser

VOID = {"input", "br", "meta", "img", "hr", "link"}

class El:
    __slots__ = ("tag", "attrs", "kids", "parent", "text")
    def __init__(s, tag, attrs, parent):
        s.tag, s.attrs, s.kids, s.parent, s.text = tag, dict(attrs), [], parent, []
    def all(s):
        yield s
        for k in s.kids:
            if isinstance(k, El):
                yield from k.all()
    def txt(s):
        return "".join(k if isinstance(k, str) else k.txt() for k in s.kids)

class P(HTMLParser):
    def __init__(s):
        super().__init__(convert_charrefs=True)
        s.root = El("#doc", [], None); s.cur = s.root
    def handle_starttag(s, tag, attrs):
        e = El(tag, attrs, s.cur); s.cur.kids.append(e)
        if tag not in VOID: s.cur = e
    def handle_endtag(s, tag):
        c = s.cur
        while c is not None and c.tag != tag: c = c.parent
        if c is not None and c.parent is not None: s.cur = c.parent
    def handle_data(s, d):
        s.cur.kids.append(d)

def norm(t): return " ".join(t.split())

class Page:
    def __init__(s, url, method="GET", body=None):
        data = body.encode() if body is not None else None
        req = urllib.request.Request(url, data=data, method=method)
        try:
            r = urllib.request.urlopen(req)
        except urllib.error.HTTPError as e:
            r = e
        s.url = r.geturl() if hasattr(r, "geturl") else url
        p = P(); p.feed(r.read().decode()); s.root = p.root
        s.values = {}
        for e in s.root.all():
            if e.tag == "input":
                t = e.attrs.get("type", "text")
                if t in ("checkbox", "radio"):
                    s.values[id(e)] = "checked" in e.attrs
                else:
                    s.values[id(e)] = e.attrs.get("value", "")
            elif e.tag == "textarea":
                s.values[id(e)] = e.txt()
            elif e.tag == "select":
                opts = [o for o in e.all() if o.tag == "option"]
                sel = [o for o in opts if "selected" in o.attrs] or opts[:1]
                s.values[id(e)] = sel[0].attrs.get("value", sel[0].txt()) if sel else ""
    def control(s, label):
        for l in s.root.all():
            if l.tag == "label" and norm(l.txt()) == label:
                if "for" in l.attrs:
                    for e in s.root.all():
                        if e.attrs.get("id") == l.attrs["for"]:
                            return e
                for e in l.all():
                    if e.tag in ("input", "select", "textarea"):
                        return e
        raise LookupError("no control labelled " + label)
    def form_of(s, e):
        while e is not None and e.tag != "form": e = e.parent
        return e
    def submit(s, form):
        pairs = []
        for e in form.all():
            n = e.attrs.get("name")
            if not n or e.tag not in ("input", "select", "textarea"): continue
            t = e.attrs.get("type", "text")
            if t in ("checkbox", "radio"):
                if s.values[id(e)]: pairs.append((n, e.attrs.get("value", "on")))
            elif t in ("submit", "button"):
                continue
            else:
                pairs.append((n, s.values[id(e)]))
        enc = urllib.parse.urlencode(pairs)
        action = urllib.parse.urljoin(s.url, form.attrs.get("action", s.url))
        if form.attrs.get("method", "get").lower() == "post":
            return Page(action, "POST", enc)
        return Page(action + "?" + enc)

def run(plan):
    page, answer = None, ""
    for line in plan.splitlines():
        st = line.split("\t")
        op = st[0]
        if op == "open": page = Page(st[1])
        elif op == "fill": page.values[id(page.control(st[1]))] = st[2]
        elif op == "check":
            e = page.control(st[1])
            if e.attrs.get("type") == "radio":
                for o in page.root.all():
                    if o.tag == "input" and o.attrs.get("name") == e.attrs.get("name"): page.values[id(o)] = False
            page.values[id(e)] = True
        elif op == "select":
            e = page.control(st[1])
            for o in e.all():
                if o.tag == "option" and norm(o.txt()) == st[2]: page.values[id(e)] = o.attrs.get("value", st[2])
        elif op == "click" and st[1] == "button":
            b = next(e for e in page.root.all() if e.tag == "button" and norm(e.txt()) == st[2])
            page = page.submit(page.form_of(b))
        elif op == "click" and st[1] == "link":
            a = next(e for e in page.root.all() if e.tag == "a" and norm(e.txt()) == st[2])
            page = Page(urllib.parse.urljoin(page.url, a.attrs["href"]))
        elif op == "read":
            answer = norm(next(e for e in page.root.all() if e.attrs.get("id") == st[1]).txt())
        elif op == "cell":
            for tr in page.root.all():
                if tr.tag != "tr": continue
                tds = [e for e in tr.kids if isinstance(e, El) and e.tag == "td"]
                if tds and norm(tds[0].txt()) == st[1]:
                    answer = norm(tds[int(st[2]) - 1].txt())
    return answer

if __name__ == "__main__":
    print("answer\t" + run(sys.stdin.read()))
