class S_QUEUE [G]

inherit
  ANY
    redefine
      default_create
    end

feature
  default_create
    do
      create queue_.make
    end

feature
  enqueue (v: G)
    do
      queue_.extend (v)
    ensure
      count = old count + 1
    end

  item: G
    require
      count > 0
    do
      Result := queue_.item
    end

  dequeue
    require
      count > 0
    do
      queue_.remove
    ensure
      count = old count - 1
    end

feature
  is_empty: BOOLEAN
    do
      Result := queue_.is_empty
    ensure
      Result = (count = 0)
    end

  count: INTEGER
    do
      Result := queue_.count
    end

feature {NONE}
  queue_: LINKED_QUEUE [G]

end

