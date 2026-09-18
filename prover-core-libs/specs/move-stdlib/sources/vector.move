module std::vector_spec {
  use std::vector;

  #[mode(spec), ext(spec(prove))]
  fun singleton_spec<Element>(e: Element): vector<Element> {
        let result = vector::singleton(e);
        result
  }

  #[mode(spec), ext(spec(prove))]
  fun reverse_spec<Element>(v: &mut vector<Element>) {
        vector::reverse(v);
  }

  #[mode(spec), ext(spec(prove))]
  fun append_spec<Element>(lhs: &mut vector<Element>, other: vector<Element>) {
        vector::append(lhs, other);
  }

  #[mode(spec), ext(spec(prove))]
  fun is_empty_spec<Element>(v: &vector<Element>): bool {
        let result = vector::is_empty(v);
        result
  }

  #[mode(spec), ext(spec(prove))]
  fun contains_spec<Element>(v: &vector<Element>, e: &Element): bool {
        let result = vector::contains(v, e);
        result
  }

  #[mode(spec), ext(spec(prove))]
  fun index_of_spec<Element>(v: &vector<Element>, e: &Element): (bool, u64) {
        let (b, idx) = vector::index_of(v, e);
        (b, idx)
  }

  #[mode(spec), ext(spec(prove))]
  fun remove_spec<Element>(v: &mut vector<Element>, i: u64): Element {
        let result = vector::remove(v, i);
        result
  }

  #[mode(spec), ext(spec(prove))]
  fun insert_spec<Element>(v: &mut vector<Element>, e: Element, i: u64) {
        vector::insert(v, e, i);
  }

  #[mode(spec), ext(spec(prove))]
  fun swap_remove_spec<Element>(v: &mut vector<Element>, i: u64): Element {
        let result = vector::swap_remove(v, i);
        result
  }

  #[mode(spec), ext(spec(prove))]
  fun skip_spec<T: drop>(v: vector<T>, n: u64): vector<T> {
        let result = vector::skip(v, n);
        result
  }

  #[mode(spec), ext(spec(prove))]
  fun take_spec<T: drop>(v: vector<T>, n: u64): vector<T> {
        let result = vector::take(v, n);
        result
  }

  #[mode(spec), ext(spec(prove))]
  fun flatten_spec<T>(v: vector<vector<T>>): vector<T> {
        let result = vector::flatten(v);
        result
  }
}
