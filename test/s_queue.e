class S_QUEUE

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
  enqueue (v: REQUEST)
    do
      queue_.extend (v)
    ensure
      count = old count + 1
    end

  item: REQUEST

  dequeue
    require
      count > 0
    do
      item := queue_.item
      queue_.remove
    ensure
      item /= Void
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
  queue_: LINKED_QUEUE [REQUEST]

end

