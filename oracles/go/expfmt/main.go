// Op: parse. The input is a JSON object whose "text" is a page in Prometheus's text exposition
// format, 0.0.4, as Lanes renders it; the answer is what expfmt's TextParser, with the format's
// names (legacy validation), reads from it: the families by name, each with its help, its type
// and its series in order, a series' labels sorted by name. Numbers are written as the shortest
// decimal that reads back as the float64 Go holds ('f', -1), so the two sides compare values.
package main

import (
	"encoding/json"
	"math"
	"sort"
	"strconv"
	"strings"

	dto "github.com/prometheus/client_model/go"
	"github.com/prometheus/common/expfmt"
	"github.com/prometheus/common/model"

	"lanes/oracles/internal/cases"
)

type series struct {
	Labels  [][2]string `json:"labels"`
	Value   *string     `json:"value,omitempty"`
	Buckets [][2]string `json:"buckets,omitempty"`
	Sum     *string     `json:"sum,omitempty"`
	Count   *string     `json:"count,omitempty"`
}

type family struct {
	Name   string   `json:"name"`
	Help   string   `json:"help"`
	Type   string   `json:"type"`
	Series []series `json:"series"`
}

func number(v float64) string {
	if math.IsInf(v, 1) {
		return "+Inf"
	}
	return strconv.FormatFloat(v, 'f', -1, 64)
}

func ptr(s string) *string { return &s }

func labels(m *dto.Metric) [][2]string {
	out := [][2]string{}
	for _, l := range m.GetLabel() {
		out = append(out, [2]string{l.GetName(), l.GetValue()})
	}
	sort.Slice(out, func(i, j int) bool { return out[i][0] < out[j][0] })
	return out
}

func read(mf *dto.MetricFamily) family {
	f := family{Name: mf.GetName(), Help: mf.GetHelp(), Type: strings.ToLower(mf.GetType().String()),
		Series: []series{}}
	for _, m := range mf.GetMetric() {
		s := series{Labels: labels(m)}
		switch mf.GetType() {
		case dto.MetricType_COUNTER:
			s.Value = ptr(number(m.GetCounter().GetValue()))
		case dto.MetricType_GAUGE:
			s.Value = ptr(number(m.GetGauge().GetValue()))
		case dto.MetricType_HISTOGRAM:
			h := m.GetHistogram()
			s.Buckets = [][2]string{}
			for _, b := range h.GetBucket() {
				s.Buckets = append(s.Buckets,
					[2]string{number(b.GetUpperBound()), strconv.FormatUint(b.GetCumulativeCount(), 10)})
			}
			s.Sum = ptr(number(h.GetSampleSum()))
			s.Count = ptr(strconv.FormatUint(h.GetSampleCount(), 10))
		default:
			s.Value = ptr(number(m.GetUntyped().GetValue()))
		}
		f.Series = append(f.Series, s)
	}
	return f
}

func main() {
	cases.Run(func(op string, in []byte) (any, bool) {
		if op != "parse" {
			panic("unknown op " + op)
		}
		var page struct {
			Text string `json:"text"`
		}
		if err := json.Unmarshal(in, &page); err != nil {
			return nil, false
		}
		parser := expfmt.NewTextParser(model.LegacyValidation)
		families, err := parser.TextToMetricFamilies(strings.NewReader(page.Text))
		if err != nil {
			return nil, false
		}
		names := make([]string, 0, len(families))
		for name := range families {
			names = append(names, name)
		}
		sort.Strings(names)
		out := []family{}
		for _, name := range names {
			out = append(out, read(families[name]))
		}
		return out, true
	})
}
