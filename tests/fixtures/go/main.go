package main

import (
	"encoding/json"
	"fmt"
	"os"
	"reflect"
)

type Record struct {
	Count int32
	Next *Record
	Values []float64
}

type Scorer interface { Score() int32 }

type First int32
type Second int32

func (value First) Score() int32 { return int32(value) + 1 }
func (value Second) Score() int32 { return int32(value) * 2 }

//go:noinline
func boxed[T Scorer](value T) Scorer { return value }

//go:noinline
func generic[T Scorer](value T) (*T, int32) {
	pointer := new(T)
	*pointer = value
	_ = boxed(value).Score()
	return pointer, value.Score()
}

//go:noinline
func (r *Record) Score() int32 { return r.Count }

//go:noinline
func score(s Scorer) int32 { return s.Score() }

//go:noinline
func allocate(count int32) *Record { return &Record{Count: count} }

//go:noinline
func records(length int) []Record {
	values := make([]Record, length, length+2)
	values[length-1].Count = 23
	return values
}

func main() {
	r := allocate(17)
	r.Values = []float64{1, 2}
	fmt.Fprintln(os.Stderr, score(r), records(len(os.Args))[0].Count)
	first, firstScore := generic(First(3))
	second, secondScore := generic(Second(5))
	fmt.Fprintln(os.Stderr, *first, firstScore, *second, secondScore)
	t := reflect.TypeOf(*r)
	json.NewEncoder(os.Stdout).Encode(map[string]any{
		"name": "main.Record", "size": t.Size(), "alignment": t.Align(),
		"fields": []uintptr{t.Field(0).Offset, t.Field(1).Offset, t.Field(2).Offset},
	})
}
