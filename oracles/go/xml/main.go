// Op: parse (the bytes of a document in, its root element out). encoding/xml's Decoder in its
// strict mode reads every token, and the document must be one element with only blanks, comments,
// processing instructions and directives around it, as XML 1.0's `document` production says
// (the Decoder reads tokens and leaves that to its caller). The tree is read again with RawToken,
// so that a name is the one written, prefix included: an element is {"name", "content"}, its
// content the elements and texts inside it in order, adjacent texts joined and comments and
// processing instructions left out.
package main

import (
	"bytes"
	"encoding/xml"
	"io"
	"strings"

	"lanes/oracles/internal/cases"
)

type element struct {
	Name    string `json:"name"`
	Content []any  `json:"content"`
}

func blank(s string) bool {
	return strings.Trim(s, " \t\r\n") == ""
}

func wellFormed(in []byte) bool {
	d := xml.NewDecoder(bytes.NewReader(in))
	depth, roots := 0, 0
	for {
		t, err := d.Token()
		if err == io.EOF {
			return depth == 0 && roots == 1
		}
		if err != nil {
			return false
		}
		switch t := t.(type) {
		case xml.StartElement:
			if depth == 0 {
				roots++
			}
			depth++
		case xml.EndElement:
			depth--
		case xml.CharData:
			if depth == 0 && !blank(string(t)) {
				return false
			}
		}
	}
}

func name(n xml.Name) string {
	if n.Space == "" {
		return n.Local
	}
	return n.Space + ":" + n.Local
}

func appendText(content []any, s string) []any {
	if n := len(content); n > 0 {
		if last, ok := content[n-1].(string); ok {
			content[n-1] = last + s
			return content
		}
	}
	return append(content, s)
}

func tree(in []byte) *element {
	d := xml.NewDecoder(bytes.NewReader(in))
	var stack []*element
	var root *element
	for {
		t, err := d.RawToken()
		if err != nil {
			return root
		}
		switch t := t.(type) {
		case xml.StartElement:
			stack = append(stack, &element{Name: name(t.Name), Content: []any{}})
		case xml.EndElement:
			done := stack[len(stack)-1]
			stack = stack[:len(stack)-1]
			if len(stack) == 0 {
				root = done
			} else {
				parent := stack[len(stack)-1]
				parent.Content = append(parent.Content, done)
			}
		case xml.CharData:
			if len(stack) > 0 {
				top := stack[len(stack)-1]
				top.Content = appendText(top.Content, string(t))
			}
		}
	}
}

func main() {
	cases.Run(func(op string, in []byte) (any, bool) {
		if op != "parse" {
			panic("unknown op " + op)
		}
		if !wellFormed(in) {
			return nil, false
		}
		return tree(in), true
	})
}
