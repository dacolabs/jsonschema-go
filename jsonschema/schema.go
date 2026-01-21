// Copyright 2025 The JSON Schema Go Project Authors. All rights reserved.
// Use of this source code is governed by an MIT-style
// license that can be found in the LICENSE file.

package jsonschema

import (
	"bytes"
	"cmp"
	"encoding/json"
	"errors"
	"fmt"
	"iter"
	"maps"
	"math"
	"reflect"
	"slices"

	"gopkg.in/yaml.v3"
)

// A Schema is a JSON schema object.
// It supports both draft-07 and the 2020-12 draft specifications:
//   - Draft-07: https://json-schema.org/draft-07/draft-handrews-json-schema-01
//     and https://json-schema.org/draft-07/draft-handrews-json-schema-validation-01
//   - Draft 2020-12: https://json-schema.org/draft/2020-12/draft-bhutton-json-schema-01
//     and https://json-schema.org/draft/2020-12/draft-bhutton-json-schema-validation-01
//
// A Schema value may have non-zero values for more than one field:
// all relevant non-zero fields are used for validation.
// There is one exception to provide more Go type-safety: the Type and Types fields
// are mutually exclusive.
//
// Since this struct is a Go representation of a JSON value, it inherits JSON's
// distinction between nil and empty. Nil slices and maps are considered absent,
// but empty ones are present and affect validation. For example,
//
//	Schema{Enum: nil}
//
// is equivalent to an empty schema, so it validates every instance. But
//
//	Schema{Enum: []any{}}
//
// requires equality to some slice element, so it vacuously rejects every instance.
type Schema struct {
	// core
	ID          string             `json:"$id,omitempty" yaml:"$id,omitempty"`
	Schema      string             `json:"$schema,omitempty" yaml:"$schema,omitempty"`
	Ref         string             `json:"$ref,omitempty" yaml:"$ref,omitempty"`
	Comment     string             `json:"$comment,omitempty" yaml:"$comment,omitempty"`
	Defs        map[string]*Schema `json:"$defs,omitempty" yaml:"$defs,omitempty"`
	Definitions map[string]*Schema `json:"definitions,omitempty" yaml:"definitions,omitempty"`

	// split draft 7 Dependencies into DependencySchemas and DependencyStrings
	DependencySchemas map[string]*Schema  `json:"-" yaml:"-"`
	DependencyStrings map[string][]string `json:"-" yaml:"-"`

	Anchor        string          `json:"$anchor,omitempty" yaml:"$anchor,omitempty"`
	DynamicAnchor string          `json:"$dynamicAnchor,omitempty" yaml:"$dynamicAnchor,omitempty"`
	DynamicRef    string          `json:"$dynamicRef,omitempty" yaml:"$dynamicRef,omitempty"`
	Vocabulary    map[string]bool `json:"$vocabulary,omitempty" yaml:"$vocabulary,omitempty"`

	// metadata
	Title       string          `json:"title,omitempty" yaml:"title,omitempty"`
	Description string          `json:"description,omitempty" yaml:"description,omitempty"`
	Default     json.RawMessage `json:"default,omitempty" yaml:"default,omitempty"`
	Deprecated  bool            `json:"deprecated,omitempty" yaml:"deprecated,omitempty"`
	ReadOnly    bool            `json:"readOnly,omitempty" yaml:"readOnly,omitempty"`
	WriteOnly   bool            `json:"writeOnly,omitempty" yaml:"writeOnly,omitempty"`
	Examples    []any           `json:"examples,omitempty" yaml:"examples,omitempty"`

	// validation
	// Use Type for a single type, or Types for multiple types; never both.
	Type  string   `json:"-" yaml:"-"`
	Types []string `json:"-" yaml:"-"`
	Enum  []any    `json:"enum,omitempty" yaml:"enum,omitempty"`
	// Const is *any because a JSON null (Go nil) is a valid value.
	Const            *any     `json:"const,omitempty" yaml:"const,omitempty"`
	MultipleOf       *float64 `json:"multipleOf,omitempty" yaml:"multipleOf,omitempty"`
	Minimum          *float64 `json:"minimum,omitempty" yaml:"minimum,omitempty"`
	Maximum          *float64 `json:"maximum,omitempty" yaml:"maximum,omitempty"`
	ExclusiveMinimum *float64 `json:"exclusiveMinimum,omitempty" yaml:"exclusiveMinimum,omitempty"`
	ExclusiveMaximum *float64 `json:"exclusiveMaximum,omitempty" yaml:"exclusiveMaximum,omitempty"`
	MinLength        *int     `json:"minLength,omitempty" yaml:"minLength,omitempty"`
	MaxLength        *int     `json:"maxLength,omitempty" yaml:"maxLength,omitempty"`
	Pattern          string   `json:"pattern,omitempty" yaml:"pattern,omitempty"`

	// arrays
	PrefixItems      []*Schema `json:"prefixItems,omitempty" yaml:"prefixItems,omitempty"`
	Items            *Schema   `json:"-" yaml:"-"`
	ItemsArray       []*Schema `json:"-" yaml:"-"`
	MinItems         *int      `json:"minItems,omitempty" yaml:"minItems,omitempty"`
	MaxItems         *int      `json:"maxItems,omitempty" yaml:"maxItems,omitempty"`
	AdditionalItems  *Schema   `json:"additionalItems,omitempty" yaml:"additionalItems,omitempty"`
	UniqueItems      bool      `json:"uniqueItems,omitempty" yaml:"uniqueItems,omitempty"`
	Contains         *Schema   `json:"contains,omitempty" yaml:"contains,omitempty"`
	MinContains      *int      `json:"minContains,omitempty" yaml:"minContains,omitempty"` // *int, not int: default is 1, not 0
	MaxContains      *int      `json:"maxContains,omitempty" yaml:"maxContains,omitempty"`
	UnevaluatedItems *Schema   `json:"unevaluatedItems,omitempty" yaml:"unevaluatedItems,omitempty"`

	// objects
	MinProperties         *int                `json:"minProperties,omitempty" yaml:"minProperties,omitempty"`
	MaxProperties         *int                `json:"maxProperties,omitempty" yaml:"maxProperties,omitempty"`
	Required              []string            `json:"required,omitempty" yaml:"required,omitempty"`
	DependentRequired     map[string][]string `json:"dependentRequired,omitempty" yaml:"dependentRequired,omitempty"`
	Properties            map[string]*Schema  `json:"properties,omitempty" yaml:"properties,omitempty"`
	PatternProperties     map[string]*Schema  `json:"patternProperties,omitempty" yaml:"patternProperties,omitempty"`
	AdditionalProperties  *Schema             `json:"additionalProperties,omitempty" yaml:"additionalProperties,omitempty"`
	PropertyNames         *Schema             `json:"propertyNames,omitempty" yaml:"propertyNames,omitempty"`
	UnevaluatedProperties *Schema             `json:"unevaluatedProperties,omitempty" yaml:"unevaluatedProperties,omitempty"`

	// logic
	AllOf []*Schema `json:"allOf,omitempty" yaml:"allOf,omitempty"`
	AnyOf []*Schema `json:"anyOf,omitempty" yaml:"anyOf,omitempty"`
	OneOf []*Schema `json:"oneOf,omitempty" yaml:"oneOf,omitempty"`
	Not   *Schema   `json:"not,omitempty" yaml:"not,omitempty"`

	// conditional
	If               *Schema            `json:"if,omitempty" yaml:"if,omitempty"`
	Then             *Schema            `json:"then,omitempty" yaml:"then,omitempty"`
	Else             *Schema            `json:"else,omitempty" yaml:"else,omitempty"`
	DependentSchemas map[string]*Schema `json:"dependentSchemas,omitempty" yaml:"dependentSchemas,omitempty"`

	// other
	// https://json-schema.org/draft/2020-12/draft-bhutton-json-schema-validation-00#rfc.section.8
	ContentEncoding  string  `json:"contentEncoding,omitempty" yaml:"contentEncoding,omitempty"`
	ContentMediaType string  `json:"contentMediaType,omitempty" yaml:"contentMediaType,omitempty"`
	ContentSchema    *Schema `json:"contentSchema,omitempty" yaml:"contentSchema,omitempty"`

	// https://json-schema.org/draft/2020-12/draft-bhutton-json-schema-validation-00#rfc.section.7
	Format string `json:"format,omitempty" yaml:"format,omitempty"`

	// Extra allows for additional keywords beyond those specified.
	Extra map[string]any `json:"-" yaml:"-"`

	// PropertyOrder records the ordering of properties for JSON and YAML rendering.
	//
	// During [For], PropertyOrder is set to the field order,
	// if the type used for inference is a struct.
	//
	// If PropertyOrder is set, it controls the relative ordering of properties in [Schema.MarshalJSON]
	// and [Schema.MarshalYAML]. The rendered output first lists any properties that appear in the
	// PropertyOrder slice in the order they appear, followed by all other properties that do not
	// appear in the PropertyOrder slice in an undefined but deterministic order.
	PropertyOrder []string `json:"-" yaml:"-"`
}

// falseSchema returns a new Schema tree that fails to validate any value.
func falseSchema() *Schema {
	return &Schema{Not: &Schema{}}
}

// anchorInfo records the subschema to which an anchor refers, and whether
// the anchor keyword is $anchor or $dynamicAnchor.
type anchorInfo struct {
	schema  *Schema
	dynamic bool
}

// String returns a short description of the schema.
func (s *Schema) String() string {
	if s.ID != "" {
		return s.ID
	}
	if a := cmp.Or(s.Anchor, s.DynamicAnchor); a != "" {
		return fmt.Sprintf("anchor %s", a)
	}
	return "<anonymous schema>"
}

// CloneSchemas returns a copy of s.
// The copy is shallow except for sub-schemas, which are themelves copied with CloneSchemas.
// This allows both s and s.CloneSchemas() to appear as sub-schemas of the same parent.
func (s *Schema) CloneSchemas() *Schema {
	if s == nil {
		return nil
	}
	s2 := *s
	v := reflect.ValueOf(&s2)
	for _, info := range schemaFieldInfos {
		fv := v.Elem().FieldByIndex(info.sf.Index)
		switch info.sf.Type {
		case schemaType:
			sscss := fv.Interface().(*Schema)
			fv.Set(reflect.ValueOf(sscss.CloneSchemas()))

		case schemaSliceType:
			slice := fv.Interface().([]*Schema)
			slice = slices.Clone(slice)
			for i, ss := range slice {
				slice[i] = ss.CloneSchemas()
			}
			fv.Set(reflect.ValueOf(slice))

		case schemaMapType:
			m := fv.Interface().(map[string]*Schema)
			m = maps.Clone(m)
			for k, ss := range m {
				m[k] = ss.CloneSchemas()
			}
			fv.Set(reflect.ValueOf(m))

		}
	}
	return &s2
}

func (s *Schema) basicChecks() error {
	if s.Type != "" && s.Types != nil {
		return errors.New("both Type and Types are set; at most one should be")
	}
	if s.Defs != nil && s.Definitions != nil {
		return errors.New("both Defs and Definitions are set; at most one should be")
	}
	if s.Items != nil && s.ItemsArray != nil {
		return errors.New("both Items and ItemsArray are set; at most one should be")
	}
	propertyOrderSeen := make(map[string]bool)
	for _, val := range s.PropertyOrder {
		if _, ok := propertyOrderSeen[val]; ok {
			// Duplicate found
			return fmt.Errorf("property order slice cannot contain duplicate entries, found duplicate %q", val)
		}
		propertyOrderSeen[val] = true
	}

	for key := range s.DependencySchemas {
		// Check if the key exists in the dependency strings map
		if _, exists := s.DependencyStrings[key]; exists {
			return fmt.Errorf("dependency key %q cannot be defined as both a schema and a string array", key)
		}
	}
	return nil
}

type schemaWithoutMethods Schema // doesn't implement json.{Unm,M}arshaler

func (s Schema) MarshalJSON() ([]byte, error) {
	// NOTE: Use a value receiver here to avoid the encoding/json bugs
	// described in golang/go#22967, golang/go#33993, and golang/go#55890.
	// With a pointer receiver, MarshalJSON is only called for Schema in
	// some cases (for example when the field value is addressable, or not
	// stored as a map value), which leads to inconsistent JSON encoding.
	// A value receiver makes Schema itself implement json.Marshaler and
	// ensures that encoding/json always calls this method.
	if err := s.basicChecks(); err != nil {
		return nil, err
	}
	// Marshal either Type or Types as "type".
	var typ any
	switch {
	case s.Type != "":
		typ = s.Type
	case s.Types != nil:
		typ = s.Types
	}

	var items any
	switch {
	case s.Items != nil:
		items = s.Items
	case s.ItemsArray != nil:
		items = s.ItemsArray
	}

	var dep map[string]any
	size := len(s.DependencySchemas) + len(s.DependencyStrings)
	if size > 0 {
		dep = make(map[string]any, size)
		for k, v := range s.DependencySchemas {
			dep[k] = v
		}
		for k, v := range s.DependencyStrings {
			dep[k] = v
		}
	}

	ms := struct {
		Type         any            `json:"type,omitempty"`
		Properties   json.Marshaler `json:"properties,omitempty"`
		Dependencies map[string]any `json:"dependencies,omitempty"`
		Items        any            `json:"items,omitempty"`
		*schemaWithoutMethods
	}{
		Type:                 typ,
		Dependencies:         dep,
		Items:                items,
		schemaWithoutMethods: (*schemaWithoutMethods)(&s),
	}
	// Marshal properties, even if the empty map (but not nil).
	if s.Properties != nil {
		ms.Properties = orderedProperties{
			props: s.Properties,
			order: s.PropertyOrder,
		}
	}

	bs, err := marshalStructWithMap(&ms, "Extra")
	if err != nil {
		return nil, err
	}
	// Marshal {} as true and {"not": {}} as false.
	// It is wasteful to do this here instead of earlier, but much easier.
	switch {
	case bytes.Equal(bs, []byte(`{}`)):
		bs = []byte("true")
	case bytes.Equal(bs, []byte(`{"not":true}`)):
		bs = []byte("false")
	}
	return bs, nil
}

// orderedProperties is a helper to marshal the properties map in a specific order.
type orderedProperties struct {
	props map[string]*Schema
	order []string
}

func (op orderedProperties) MarshalJSON() ([]byte, error) {
	var buf bytes.Buffer
	buf.WriteByte('{')

	first := true
	processed := make(map[string]bool, len(op.props))

	// Helper closure to write "key": value
	writeEntry := func(key string, val *Schema) error {
		if !first {
			buf.WriteByte(',')
		}
		first = false

		// Marshal the Key
		keyBytes, err := json.Marshal(key)
		if err != nil {
			return err
		}
		buf.Write(keyBytes)

		buf.WriteByte(':')

		// Marshal the Value
		valBytes, err := json.Marshal(val)
		if err != nil {
			return err
		}
		buf.Write(valBytes)
		return nil
	}

	// Write keys explicitly listed in PropertyOrder
	for _, name := range op.order {
		if prop, ok := op.props[name]; ok {
			if err := writeEntry(name, prop); err != nil {
				return nil, err
			}
			processed[name] = true
		}
	}

	// Write any remaining keys
	var remaining []string
	for name := range op.props {
		if !processed[name] {
			remaining = append(remaining, name)
		}
	}

	// Sort the slice alphabetically
	slices.Sort(remaining)

	for _, name := range remaining {
		if err := writeEntry(name, op.props[name]); err != nil {
			return nil, err
		}
	}

	buf.WriteByte('}')
	return buf.Bytes(), nil
}

func (s *Schema) UnmarshalJSON(data []byte) error {
	// A JSON boolean is a valid schema.
	var b bool
	if err := json.Unmarshal(data, &b); err == nil {
		if b {
			// true is the empty schema, which validates everything.
			*s = Schema{}
		} else {
			// false is the schema that validates nothing.
			*s = *falseSchema()
		}
		return nil
	}

	ms := struct {
		Type          json.RawMessage            `json:"type,omitempty"`
		Dependencies  map[string]json.RawMessage `json:"dependencies,omitempty"`
		Items         json.RawMessage            `json:"items,omitempty"`
		Const         json.RawMessage            `json:"const,omitempty"`
		MinLength     *integer                   `json:"minLength,omitempty"`
		MaxLength     *integer                   `json:"maxLength,omitempty"`
		MinItems      *integer                   `json:"minItems,omitempty"`
		MaxItems      *integer                   `json:"maxItems,omitempty"`
		MinProperties *integer                   `json:"minProperties,omitempty"`
		MaxProperties *integer                   `json:"maxProperties,omitempty"`
		MinContains   *integer                   `json:"minContains,omitempty"`
		MaxContains   *integer                   `json:"maxContains,omitempty"`

		*schemaWithoutMethods
	}{
		schemaWithoutMethods: (*schemaWithoutMethods)(s),
	}
	if err := unmarshalStructWithMap(data, &ms, "Extra"); err != nil {
		return err
	}
	// Unmarshal "type" as either Type or Types.
	var err error
	if len(ms.Type) > 0 {
		switch ms.Type[0] {
		case '"':
			err = json.Unmarshal(ms.Type, &s.Type)
		case '[':
			err = json.Unmarshal(ms.Type, &s.Types)
		default:
			err = fmt.Errorf(`invalid value for "type": %q`, ms.Type)
		}
	}
	if err != nil {
		return err
	}

	// Unmarshal "items" as either Items or ItemsArray.
	if len(ms.Items) > 0 {
		switch ms.Items[0] {
		case '[':
			var schemas []*Schema
			err = json.Unmarshal(ms.Items, &schemas)
			s.ItemsArray = schemas
		default:
			var schema Schema
			err = json.Unmarshal(ms.Items, &schema)
			s.Items = &schema
		}
	}
	if err != nil {
		return err
	}

	// Unmarshal "Dependencies" values as either string arrays or schemas
	// and assign them to specific map DependencySchemas or DependencyStrings.
	for k, v := range ms.Dependencies {
		if len(v) > 0 {
			switch v[0] {
			case '[':
				var dstrings []string
				err = json.Unmarshal(v, &dstrings)
				if s.DependencyStrings == nil {
					s.DependencyStrings = make(map[string][]string)
				}
				s.DependencyStrings[k] = dstrings
			default:
				var dschema Schema
				err = json.Unmarshal(v, &dschema)
				if s.DependencySchemas == nil {
					s.DependencySchemas = make(map[string]*Schema)
				}
				s.DependencySchemas[k] = &dschema
			}
		}
		if err != nil {
			return err
		}
	}

	unmarshalAnyPtr := func(p **any, raw json.RawMessage) error {
		if len(raw) == 0 {
			return nil
		}
		if bytes.Equal(raw, []byte("null")) {
			*p = new(any)
			return nil
		}
		return json.Unmarshal(raw, p)
	}

	// Setting Const to a pointer to null will marshal properly, but won't
	// unmarshal: the *any is set to nil, not a pointer to nil.
	if err := unmarshalAnyPtr(&s.Const, ms.Const); err != nil {
		return err
	}

	set := func(dst **int, src *integer) {
		if src != nil {
			*dst = Ptr(int(*src))
		}
	}

	set(&s.MinLength, ms.MinLength)
	set(&s.MaxLength, ms.MaxLength)
	set(&s.MinItems, ms.MinItems)
	set(&s.MaxItems, ms.MaxItems)
	set(&s.MinProperties, ms.MinProperties)
	set(&s.MaxProperties, ms.MaxProperties)
	set(&s.MinContains, ms.MinContains)
	set(&s.MaxContains, ms.MaxContains)

	return nil
}

// MarshalYAML implements yaml.Marshaler.
// It mirrors the behavior of MarshalJSON, including:
// - Boolean schema representation (empty schema → true, {not: {}} → false)
// - Union field handling (Type/Types, Items/ItemsArray, DependencySchemas/DependencyStrings)
// - Property ordering via PropertyOrder
// - Extra fields
func (s Schema) MarshalYAML() (any, error) {
	if err := s.basicChecks(); err != nil {
		return nil, err
	}

	// Check for boolean schemas.
	// Empty schema → true, Schema{Not: &Schema{}} → false
	if isEmptySchema(s) {
		return true, nil
	}
	if isFalseSchema(s) {
		return false, nil
	}

	node := &yaml.Node{Kind: yaml.MappingNode}

	// addField adds a key-value pair to the mapping node if value is non-zero.
	addField := func(key string, value any) error {
		if isZeroValue(reflect.ValueOf(value)) {
			return nil
		}
		keyNode := &yaml.Node{Kind: yaml.ScalarNode, Value: key}
		var valueNode yaml.Node
		if err := valueNode.Encode(value); err != nil {
			return err
		}
		node.Content = append(node.Content, keyNode, &valueNode)
		return nil
	}

	// Marshal fields in schema order, handling union fields specially.
	// Core fields
	if err := addField("$id", s.ID); err != nil {
		return nil, err
	}
	if err := addField("$schema", s.Schema); err != nil {
		return nil, err
	}
	if err := addField("$ref", s.Ref); err != nil {
		return nil, err
	}
	if err := addField("$comment", s.Comment); err != nil {
		return nil, err
	}
	if err := addField("$defs", s.Defs); err != nil {
		return nil, err
	}
	if err := addField("definitions", s.Definitions); err != nil {
		return nil, err
	}

	// Dependencies: merge DependencySchemas and DependencyStrings into one field
	size := len(s.DependencySchemas) + len(s.DependencyStrings)
	if size > 0 {
		dep := make(map[string]any, size)
		for k, v := range s.DependencySchemas {
			dep[k] = v
		}
		for k, v := range s.DependencyStrings {
			dep[k] = v
		}
		if err := addField("dependencies", dep); err != nil {
			return nil, err
		}
	}

	if err := addField("$anchor", s.Anchor); err != nil {
		return nil, err
	}
	if err := addField("$dynamicAnchor", s.DynamicAnchor); err != nil {
		return nil, err
	}
	if err := addField("$dynamicRef", s.DynamicRef); err != nil {
		return nil, err
	}
	if err := addField("$vocabulary", s.Vocabulary); err != nil {
		return nil, err
	}

	// Metadata
	if err := addField("title", s.Title); err != nil {
		return nil, err
	}
	if err := addField("description", s.Description); err != nil {
		return nil, err
	}
	if len(s.Default) > 0 {
		var defaultVal any
		if err := json.Unmarshal(s.Default, &defaultVal); err != nil {
			return nil, err
		}
		if err := addField("default", defaultVal); err != nil {
			return nil, err
		}
	}
	if err := addField("deprecated", s.Deprecated); err != nil {
		return nil, err
	}
	if err := addField("readOnly", s.ReadOnly); err != nil {
		return nil, err
	}
	if err := addField("writeOnly", s.WriteOnly); err != nil {
		return nil, err
	}
	if err := addField("examples", s.Examples); err != nil {
		return nil, err
	}

	// Validation - Type/Types union
	switch {
	case s.Type != "":
		if err := addField("type", s.Type); err != nil {
			return nil, err
		}
	case s.Types != nil:
		if err := addField("type", s.Types); err != nil {
			return nil, err
		}
	}

	if err := addField("enum", s.Enum); err != nil {
		return nil, err
	}
	if s.Const != nil {
		if err := addField("const", *s.Const); err != nil {
			return nil, err
		}
	}
	if err := addField("multipleOf", s.MultipleOf); err != nil {
		return nil, err
	}
	if err := addField("minimum", s.Minimum); err != nil {
		return nil, err
	}
	if err := addField("maximum", s.Maximum); err != nil {
		return nil, err
	}
	if err := addField("exclusiveMinimum", s.ExclusiveMinimum); err != nil {
		return nil, err
	}
	if err := addField("exclusiveMaximum", s.ExclusiveMaximum); err != nil {
		return nil, err
	}
	if err := addField("minLength", s.MinLength); err != nil {
		return nil, err
	}
	if err := addField("maxLength", s.MaxLength); err != nil {
		return nil, err
	}
	if err := addField("pattern", s.Pattern); err != nil {
		return nil, err
	}

	// Arrays
	if err := addField("prefixItems", s.PrefixItems); err != nil {
		return nil, err
	}
	// Items/ItemsArray union
	switch {
	case s.Items != nil:
		if err := addField("items", s.Items); err != nil {
			return nil, err
		}
	case s.ItemsArray != nil:
		if err := addField("items", s.ItemsArray); err != nil {
			return nil, err
		}
	}
	if err := addField("minItems", s.MinItems); err != nil {
		return nil, err
	}
	if err := addField("maxItems", s.MaxItems); err != nil {
		return nil, err
	}
	if err := addField("additionalItems", s.AdditionalItems); err != nil {
		return nil, err
	}
	if err := addField("uniqueItems", s.UniqueItems); err != nil {
		return nil, err
	}
	if err := addField("contains", s.Contains); err != nil {
		return nil, err
	}
	if err := addField("minContains", s.MinContains); err != nil {
		return nil, err
	}
	if err := addField("maxContains", s.MaxContains); err != nil {
		return nil, err
	}
	if err := addField("unevaluatedItems", s.UnevaluatedItems); err != nil {
		return nil, err
	}

	// Objects
	if err := addField("minProperties", s.MinProperties); err != nil {
		return nil, err
	}
	if err := addField("maxProperties", s.MaxProperties); err != nil {
		return nil, err
	}
	if err := addField("required", s.Required); err != nil {
		return nil, err
	}
	if err := addField("dependentRequired", s.DependentRequired); err != nil {
		return nil, err
	}

	// Properties with PropertyOrder support
	if s.Properties != nil {
		propsNode, err := marshalPropertiesYAML(s.Properties, s.PropertyOrder)
		if err != nil {
			return nil, err
		}
		keyNode := &yaml.Node{Kind: yaml.ScalarNode, Value: "properties"}
		node.Content = append(node.Content, keyNode, propsNode)
	}

	if err := addField("patternProperties", s.PatternProperties); err != nil {
		return nil, err
	}
	if err := addField("additionalProperties", s.AdditionalProperties); err != nil {
		return nil, err
	}
	if err := addField("propertyNames", s.PropertyNames); err != nil {
		return nil, err
	}
	if err := addField("unevaluatedProperties", s.UnevaluatedProperties); err != nil {
		return nil, err
	}

	// Logic
	if err := addField("allOf", s.AllOf); err != nil {
		return nil, err
	}
	if err := addField("anyOf", s.AnyOf); err != nil {
		return nil, err
	}
	if err := addField("oneOf", s.OneOf); err != nil {
		return nil, err
	}
	if err := addField("not", s.Not); err != nil {
		return nil, err
	}

	// Conditional
	if err := addField("if", s.If); err != nil {
		return nil, err
	}
	if err := addField("then", s.Then); err != nil {
		return nil, err
	}
	if err := addField("else", s.Else); err != nil {
		return nil, err
	}
	if err := addField("dependentSchemas", s.DependentSchemas); err != nil {
		return nil, err
	}

	// Other
	if err := addField("contentEncoding", s.ContentEncoding); err != nil {
		return nil, err
	}
	if err := addField("contentMediaType", s.ContentMediaType); err != nil {
		return nil, err
	}
	if err := addField("contentSchema", s.ContentSchema); err != nil {
		return nil, err
	}
	if err := addField("format", s.Format); err != nil {
		return nil, err
	}

	// Extra fields (sorted for determinism)
	// Note: We don't use addField here because Extra fields should always be output,
	// even if they have zero values (e.g., "extra: 0" should not be omitted).
	keys := make([]string, 0, len(s.Extra))
	for k := range s.Extra {
		keys = append(keys, k)
	}
	slices.Sort(keys)
	for _, k := range keys {
		keyNode := &yaml.Node{Kind: yaml.ScalarNode, Value: k}
		var valueNode yaml.Node
		if err := valueNode.Encode(s.Extra[k]); err != nil {
			return nil, err
		}
		node.Content = append(node.Content, keyNode, &valueNode)
	}

	return node, nil
}

// marshalPropertiesYAML marshals the properties map to a YAML node with ordering.
func marshalPropertiesYAML(props map[string]*Schema, order []string) (*yaml.Node, error) {
	node := &yaml.Node{Kind: yaml.MappingNode}

	processed := make(map[string]bool, len(props))

	// First, add properties in PropertyOrder
	for _, name := range order {
		if prop, ok := props[name]; ok {
			keyNode := &yaml.Node{Kind: yaml.ScalarNode, Value: name}
			var valueNode yaml.Node
			if err := valueNode.Encode(prop); err != nil {
				return nil, err
			}
			node.Content = append(node.Content, keyNode, &valueNode)
			processed[name] = true
		}
	}

	// Then add remaining properties in sorted order
	var remaining []string
	for name := range props {
		if !processed[name] {
			remaining = append(remaining, name)
		}
	}
	slices.Sort(remaining)

	for _, name := range remaining {
		keyNode := &yaml.Node{Kind: yaml.ScalarNode, Value: name}
		var valueNode yaml.Node
		if err := valueNode.Encode(props[name]); err != nil {
			return nil, err
		}
		node.Content = append(node.Content, keyNode, &valueNode)
	}

	return node, nil
}

// isEmptySchema checks if s is the empty schema (validates everything).
func isEmptySchema(s Schema) bool {
	return reflect.DeepEqual(s, Schema{})
}

// isFalseSchema checks if s is the false schema (validates nothing).
// The false schema is represented as {not: {}}.
func isFalseSchema(s Schema) bool {
	if s.Not == nil {
		return false
	}
	// Check that Not is an empty schema and all other fields are zero
	sCopy := s
	sCopy.Not = nil
	return isEmptySchema(*s.Not) && isEmptySchema(sCopy)
}

// isZeroValue reports whether v is the zero value for its type.
func isZeroValue(v reflect.Value) bool {
	if !v.IsValid() {
		return true
	}
	switch v.Kind() {
	case reflect.Bool:
		return !v.Bool()
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		return v.Int() == 0
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
		return v.Uint() == 0
	case reflect.Float32, reflect.Float64:
		return v.Float() == 0
	case reflect.String:
		return v.String() == ""
	case reflect.Slice, reflect.Map:
		return v.IsNil()
	case reflect.Ptr, reflect.Interface:
		return v.IsNil()
	default:
		return false
	}
}

// UnmarshalYAML implements yaml.Unmarshaler.
// It mirrors the behavior of UnmarshalJSON, including:
// - Boolean schema representation (true → empty schema, false → {not: {}})
// - Union field handling (type, items, dependencies)
// - Extra fields
func (s *Schema) UnmarshalYAML(node *yaml.Node) error {
	// Handle boolean schemas
	if node.Kind == yaml.ScalarNode {
		if node.Tag == "!!bool" {
			if node.Value == "true" {
				*s = Schema{}
				return nil
			}
			if node.Value == "false" {
				*s = *falseSchema()
				return nil
			}
		}
		return fmt.Errorf("expected mapping or boolean, got scalar: %s", node.Value)
	}

	if node.Kind != yaml.MappingNode {
		return fmt.Errorf("expected mapping or boolean, got kind %v", node.Kind)
	}

	// First pass: decode into schemaWithoutMethods to get most fields
	// We need to handle union fields and Extra separately
	type rawSchema struct {
		ID          string             `yaml:"$id,omitempty"`
		Schema      string             `yaml:"$schema,omitempty"`
		Ref         string             `yaml:"$ref,omitempty"`
		Comment     string             `yaml:"$comment,omitempty"`
		Defs        map[string]*Schema `yaml:"$defs,omitempty"`
		Definitions map[string]*Schema `yaml:"definitions,omitempty"`

		Anchor        string          `yaml:"$anchor,omitempty"`
		DynamicAnchor string          `yaml:"$dynamicAnchor,omitempty"`
		DynamicRef    string          `yaml:"$dynamicRef,omitempty"`
		Vocabulary    map[string]bool `yaml:"$vocabulary,omitempty"`

		Title       string `yaml:"title,omitempty"`
		Description string `yaml:"description,omitempty"`
		Default     any    `yaml:"default,omitempty"`
		Deprecated  bool   `yaml:"deprecated,omitempty"`
		ReadOnly    bool   `yaml:"readOnly,omitempty"`
		WriteOnly   bool   `yaml:"writeOnly,omitempty"`
		Examples    []any  `yaml:"examples,omitempty"`

		Enum       []any    `yaml:"enum,omitempty"`
		Const      *any     `yaml:"const,omitempty"`
		MultipleOf *float64 `yaml:"multipleOf,omitempty"`
		Minimum    *float64 `yaml:"minimum,omitempty"`
		Maximum    *float64 `yaml:"maximum,omitempty"`

		ExclusiveMinimum *float64 `yaml:"exclusiveMinimum,omitempty"`
		ExclusiveMaximum *float64 `yaml:"exclusiveMaximum,omitempty"`
		MinLength        *int     `yaml:"minLength,omitempty"`
		MaxLength        *int     `yaml:"maxLength,omitempty"`
		Pattern          string   `yaml:"pattern,omitempty"`

		PrefixItems      []*Schema `yaml:"prefixItems,omitempty"`
		MinItems         *int      `yaml:"minItems,omitempty"`
		MaxItems         *int      `yaml:"maxItems,omitempty"`
		AdditionalItems  *Schema   `yaml:"additionalItems,omitempty"`
		UniqueItems      bool      `yaml:"uniqueItems,omitempty"`
		Contains         *Schema   `yaml:"contains,omitempty"`
		MinContains      *int      `yaml:"minContains,omitempty"`
		MaxContains      *int      `yaml:"maxContains,omitempty"`
		UnevaluatedItems *Schema   `yaml:"unevaluatedItems,omitempty"`

		MinProperties         *int                `yaml:"minProperties,omitempty"`
		MaxProperties         *int                `yaml:"maxProperties,omitempty"`
		Required              []string            `yaml:"required,omitempty"`
		DependentRequired     map[string][]string `yaml:"dependentRequired,omitempty"`
		Properties            map[string]*Schema  `yaml:"properties,omitempty"`
		PatternProperties     map[string]*Schema  `yaml:"patternProperties,omitempty"`
		AdditionalProperties  *Schema             `yaml:"additionalProperties,omitempty"`
		PropertyNames         *Schema             `yaml:"propertyNames,omitempty"`
		UnevaluatedProperties *Schema             `yaml:"unevaluatedProperties,omitempty"`

		AllOf            []*Schema          `yaml:"allOf,omitempty"`
		AnyOf            []*Schema          `yaml:"anyOf,omitempty"`
		OneOf            []*Schema          `yaml:"oneOf,omitempty"`
		Not              *Schema            `yaml:"not,omitempty"`
		If               *Schema            `yaml:"if,omitempty"`
		Then             *Schema            `yaml:"then,omitempty"`
		Else             *Schema            `yaml:"else,omitempty"`
		DependentSchemas map[string]*Schema `yaml:"dependentSchemas,omitempty"`

		ContentEncoding  string  `yaml:"contentEncoding,omitempty"`
		ContentMediaType string  `yaml:"contentMediaType,omitempty"`
		ContentSchema    *Schema `yaml:"contentSchema,omitempty"`
		Format           string  `yaml:"format,omitempty"`
	}

	var raw rawSchema
	if err := node.Decode(&raw); err != nil {
		return err
	}

	// Copy basic fields
	s.ID = raw.ID
	s.Schema = raw.Schema
	s.Ref = raw.Ref
	s.Comment = raw.Comment
	s.Defs = raw.Defs
	s.Definitions = raw.Definitions
	s.Anchor = raw.Anchor
	s.DynamicAnchor = raw.DynamicAnchor
	s.DynamicRef = raw.DynamicRef
	s.Vocabulary = raw.Vocabulary
	s.Title = raw.Title
	s.Description = raw.Description
	s.Deprecated = raw.Deprecated
	s.ReadOnly = raw.ReadOnly
	s.WriteOnly = raw.WriteOnly
	s.Examples = raw.Examples
	s.Enum = raw.Enum
	s.Const = raw.Const
	s.MultipleOf = raw.MultipleOf
	s.Minimum = raw.Minimum
	s.Maximum = raw.Maximum
	s.ExclusiveMinimum = raw.ExclusiveMinimum
	s.ExclusiveMaximum = raw.ExclusiveMaximum
	s.MinLength = raw.MinLength
	s.MaxLength = raw.MaxLength
	s.Pattern = raw.Pattern
	s.PrefixItems = raw.PrefixItems
	s.MinItems = raw.MinItems
	s.MaxItems = raw.MaxItems
	s.AdditionalItems = raw.AdditionalItems
	s.UniqueItems = raw.UniqueItems
	s.Contains = raw.Contains
	s.MinContains = raw.MinContains
	s.MaxContains = raw.MaxContains
	s.UnevaluatedItems = raw.UnevaluatedItems
	s.MinProperties = raw.MinProperties
	s.MaxProperties = raw.MaxProperties
	s.Required = raw.Required
	s.DependentRequired = raw.DependentRequired
	s.Properties = raw.Properties
	s.PatternProperties = raw.PatternProperties
	s.AdditionalProperties = raw.AdditionalProperties
	s.PropertyNames = raw.PropertyNames
	s.UnevaluatedProperties = raw.UnevaluatedProperties
	s.AllOf = raw.AllOf
	s.AnyOf = raw.AnyOf
	s.OneOf = raw.OneOf
	s.Not = raw.Not
	s.If = raw.If
	s.Then = raw.Then
	s.Else = raw.Else
	s.DependentSchemas = raw.DependentSchemas
	s.ContentEncoding = raw.ContentEncoding
	s.ContentMediaType = raw.ContentMediaType
	s.ContentSchema = raw.ContentSchema
	s.Format = raw.Format

	// Handle Default - convert to json.RawMessage
	if raw.Default != nil {
		defaultBytes, err := json.Marshal(raw.Default)
		if err != nil {
			return fmt.Errorf("marshaling default: %w", err)
		}
		s.Default = defaultBytes
	}

	// Now handle union fields by inspecting the node directly
	for i := 0; i < len(node.Content); i += 2 {
		keyNode := node.Content[i]
		valueNode := node.Content[i+1]

		switch keyNode.Value {
		case "type":
			// type can be a string or array of strings
			if valueNode.Kind == yaml.ScalarNode {
				// Must be a string scalar, not a number or bool
				if valueNode.Tag != "!!str" {
					return fmt.Errorf("type must be string or array, got %s", valueNode.Value)
				}
				s.Type = valueNode.Value
			} else if valueNode.Kind == yaml.SequenceNode {
				var types []string
				if err := valueNode.Decode(&types); err != nil {
					return fmt.Errorf("decoding type array: %w", err)
				}
				s.Types = types
			} else {
				return fmt.Errorf("type must be string or array, got kind %v", valueNode.Kind)
			}

		case "items":
			// items can be a schema or array of schemas
			if valueNode.Kind == yaml.SequenceNode {
				var schemas []*Schema
				if err := valueNode.Decode(&schemas); err != nil {
					return fmt.Errorf("decoding items array: %w", err)
				}
				s.ItemsArray = schemas
			} else {
				var schema Schema
				if err := valueNode.Decode(&schema); err != nil {
					return fmt.Errorf("decoding items schema: %w", err)
				}
				s.Items = &schema
			}

		case "dependencies":
			// dependencies values can be schemas or string arrays
			if valueNode.Kind != yaml.MappingNode {
				return fmt.Errorf("dependencies must be a mapping")
			}
			for j := 0; j < len(valueNode.Content); j += 2 {
				depKey := valueNode.Content[j].Value
				depValue := valueNode.Content[j+1]

				if depValue.Kind == yaml.SequenceNode {
					// String array
					var strings []string
					if err := depValue.Decode(&strings); err != nil {
						return fmt.Errorf("decoding dependency strings for %s: %w", depKey, err)
					}
					if s.DependencyStrings == nil {
						s.DependencyStrings = make(map[string][]string)
					}
					s.DependencyStrings[depKey] = strings
				} else {
					// Schema
					var schema Schema
					if err := depValue.Decode(&schema); err != nil {
						return fmt.Errorf("decoding dependency schema for %s: %w", depKey, err)
					}
					if s.DependencySchemas == nil {
						s.DependencySchemas = make(map[string]*Schema)
					}
					s.DependencySchemas[depKey] = &schema
				}
			}
		}
	}

	// Handle Extra fields - collect unknown keys
	knownKeys := map[string]bool{
		"$id": true, "$schema": true, "$ref": true, "$comment": true,
		"$defs": true, "definitions": true, "$anchor": true, "$dynamicAnchor": true,
		"$dynamicRef": true, "$vocabulary": true, "title": true, "description": true,
		"default": true, "deprecated": true, "readOnly": true, "writeOnly": true,
		"examples": true, "type": true, "enum": true, "const": true,
		"multipleOf": true, "minimum": true, "maximum": true,
		"exclusiveMinimum": true, "exclusiveMaximum": true,
		"minLength": true, "maxLength": true, "pattern": true,
		"prefixItems": true, "items": true, "minItems": true, "maxItems": true,
		"additionalItems": true, "uniqueItems": true, "contains": true,
		"minContains": true, "maxContains": true, "unevaluatedItems": true,
		"minProperties": true, "maxProperties": true, "required": true,
		"dependentRequired": true, "properties": true, "patternProperties": true,
		"additionalProperties": true, "propertyNames": true, "unevaluatedProperties": true,
		"allOf": true, "anyOf": true, "oneOf": true, "not": true,
		"if": true, "then": true, "else": true, "dependentSchemas": true,
		"dependencies": true, "contentEncoding": true, "contentMediaType": true,
		"contentSchema": true, "format": true,
	}

	for i := 0; i < len(node.Content); i += 2 {
		keyNode := node.Content[i]
		valueNode := node.Content[i+1]
		key := keyNode.Value

		if !knownKeys[key] {
			var value any
			if err := valueNode.Decode(&value); err != nil {
				return fmt.Errorf("decoding extra field %s: %w", key, err)
			}
			if s.Extra == nil {
				s.Extra = make(map[string]any)
			}
			s.Extra[key] = value
		}
	}

	return nil
}

type integer int32 // for the integer-valued fields of Schema

func (ip *integer) UnmarshalJSON(data []byte) error {
	if len(data) == 0 {
		// nothing to do
		return nil
	}
	// If there is a decimal point, src is a floating-point number.
	var i int64
	if bytes.ContainsRune(data, '.') {
		var f float64
		if err := json.Unmarshal(data, &f); err != nil {
			return errors.New("not a number")
		}
		i = int64(f)
		if float64(i) != f {
			return errors.New("not an integer value")
		}
	} else {
		if err := json.Unmarshal(data, &i); err != nil {
			return errors.New("cannot be unmarshaled into an int")
		}
	}
	// Ensure behavior is the same on both 32-bit and 64-bit systems.
	if i < math.MinInt32 || i > math.MaxInt32 {
		return errors.New("integer is out of range")
	}
	*ip = integer(i)
	return nil
}

// Ptr returns a pointer to a new variable whose value is x.
func Ptr[T any](x T) *T { return &x }

// every applies f preorder to every schema under s including s.
// The second argument to f is the path to the schema appended to the argument path.
// It stops when f returns false.
func (s *Schema) every(f func(*Schema) bool) bool {
	return f(s) && s.everyChild(func(s *Schema) bool { return s.every(f) })
}

// everyChild reports whether f is true for every immediate child schema of s.
func (s *Schema) everyChild(f func(*Schema) bool) bool {
	v := reflect.ValueOf(s)
	for _, info := range schemaFieldInfos {
		fv := v.Elem().FieldByIndex(info.sf.Index)
		switch info.sf.Type {
		case schemaType:
			// A field that contains an individual schema. A nil is valid: it just means the field isn't present.
			c := fv.Interface().(*Schema)
			if c != nil && !f(c) {
				return false
			}

		case schemaSliceType:
			slice := fv.Interface().([]*Schema)
			for _, c := range slice {
				if !f(c) {
					return false
				}
			}

		case schemaMapType:
			// Sort keys for determinism.
			m := fv.Interface().(map[string]*Schema)
			for _, k := range slices.Sorted(maps.Keys(m)) {
				if !f(m[k]) {
					return false
				}
			}
		}
	}

	return true
}

// all wraps every in an iterator.
func (s *Schema) all() iter.Seq[*Schema] {
	return func(yield func(*Schema) bool) { s.every(yield) }
}

// children wraps everyChild in an iterator.
func (s *Schema) children() iter.Seq[*Schema] {
	return func(yield func(*Schema) bool) { s.everyChild(yield) }
}

var (
	schemaType      = reflect.TypeFor[*Schema]()
	schemaSliceType = reflect.TypeFor[[]*Schema]()
	schemaMapType   = reflect.TypeFor[map[string]*Schema]()
)

type structFieldInfo struct {
	sf       reflect.StructField
	jsonName string
}

var (
	// the visible fields of Schema that have a JSON name, sorted by that name
	schemaFieldInfos []structFieldInfo
	// map from JSON name to field
	schemaFieldMap = map[string]reflect.StructField{}
)

func init() {
	t := reflect.VisibleFields(reflect.TypeFor[Schema]())
	for _, sf := range t {
		info := fieldJSONInfo(sf)
		if !info.omit {
			schemaFieldInfos = append(schemaFieldInfos, structFieldInfo{sf, info.name})
		} else {
			// jsoninfo.name is used to build the info paths. The items and dependencies are ommited,
			// since the original fields are separated to handle the union types supported in json and
			// these fields have custom marshalling and unmarshalling logic.
			// we still need these fields in schemaFieldInfos for creating schema trees and calculating paths and refs.
			// so we manually create them and assign the jsonName to the original field json name.
			switch sf.Name {
			case "Items", "ItemsArray":
				schemaFieldInfos = append(schemaFieldInfos, structFieldInfo{sf, "items"})
			case "DependencySchemas", "DependencyStrings":
				schemaFieldInfos = append(schemaFieldInfos, structFieldInfo{sf, "dependencies"})
			}
		}
	}
	// The value of "dependencies" this sort of schemaFieldInfos.
	// This sort is unstable and is comparing the json.names of DependencyStrings and DependencySchemas which are both "dependencies".
	// Since the sort is unstable it cannot be guarantied that "dependencies" has the DependencySchemas value.
	slices.SortFunc(schemaFieldInfos, func(i1, i2 structFieldInfo) int {
		return cmp.Compare(i1.jsonName, i2.jsonName)
	})
	for _, info := range schemaFieldInfos {
		schemaFieldMap[info.jsonName] = info.sf
	}
}
