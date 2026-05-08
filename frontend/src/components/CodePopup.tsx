import { useEffect, useRef, useState } from 'react'
import SyntaxHighlighter from 'react-syntax-highlighter'
import type { TheoremNodeData } from '../data/graphData'
import type { DefinitionEntry } from '../data/definitions'

// Abyss-inspired dark theme for react-syntax-highlighter
const abyssStyle: Record<string, React.CSSProperties> = {
  'code[class*="language-"]': {
    color: '#6688cc',
    background: '#000C18',
    fontFamily: '"Fira Code", "Consolas", "Monaco", monospace',
    fontSize: '12.5px',
    lineHeight: '1.65',
    whiteSpace: 'pre',
    wordSpacing: 'normal',
    wordBreak: 'normal',
    tabSize: 2,
  } as React.CSSProperties,
  'pre[class*="language-"]': {
    color: '#6688cc',
    background: '#000C18',
    margin: 0,
    padding: '1.25rem',
    overflow: 'auto',
    borderRadius: 0,
  } as React.CSSProperties,
  comment: { color: '#384887', fontStyle: 'italic' },
  prolog: { color: '#384887' },
  doctype: { color: '#384887' },
  cdata: { color: '#384887' },
  punctuation: { color: '#6688cc' },
  keyword: { color: '#4488cc' },
  builtin: { color: '#3399cc' },
  boolean: { color: '#f280d0' },
  number: { color: '#f280d0' },
  string: { color: '#22aa44' },
  char: { color: '#22aa44' },
  regex: { color: '#22aa44' },
  'class-name': { color: '#ddbb88' },
  function: { color: '#ddbb88' },
  constant: { color: '#ddbb88' },
  symbol: { color: '#ddbb88' },
  variable: { color: '#6688cc' },
  operator: { color: '#6688cc' },
  property: { color: '#ddbb88' },
  tag: { color: '#3399cc' },
  'attr-name': { color: '#ddbb88' },
  'attr-value': { color: '#22aa44' },
  important: { color: '#ff6600', fontWeight: 'bold' },
  bold: { fontWeight: 'bold' },
  italic: { fontStyle: 'italic' },
}

const MIN_WIDTH = 300
const MAX_WIDTH_FRACTION = 0.92 // never wider than 92vw

interface CodePopupProps {
  node: TheoremNodeData | DefinitionEntry
  onClose: () => void
}

function isTheoremNode(n: TheoremNodeData | DefinitionEntry): n is TheoremNodeData {
  return 'leanCode' in n && !('description' in n)
}

export default function CodePopup({ node, onClose }: CodePopupProps) {
  const leanCode = 'leanCode' in node ? node.leanCode : (node as DefinitionEntry).leanCode
  const title = isTheoremNode(node) ? node.label : (node as DefinitionEntry).name
  const id = node.id

  // Width in pixels — starts at 50vw
  const [width, setWidth] = useState(() => Math.round(window.innerWidth * 0.5))

  // Drag state tracked in refs (no re-render needed mid-drag)
  const isDragging = useRef(false)
  const dragStartX = useRef(0)
  const dragStartWidth = useRef(0)

  // Keyboard close
  useEffect(() => {
    const handleKey = (e: KeyboardEvent) => { if (e.key === 'Escape') onClose() }
    document.addEventListener('keydown', handleKey)
    return () => document.removeEventListener('keydown', handleKey)
  }, [onClose])

  // Global mouse-move / mouse-up listeners for the drag
  useEffect(() => {
    const onMouseMove = (e: MouseEvent) => {
      if (!isDragging.current) return
      const dx = dragStartX.current - e.clientX   // dragging left → wider
      const next = Math.min(
        Math.max(dragStartWidth.current + dx, MIN_WIDTH),
        window.innerWidth * MAX_WIDTH_FRACTION,
      )
      setWidth(Math.round(next))
    }

    const onMouseUp = () => {
      if (!isDragging.current) return
      isDragging.current = false
      document.body.style.userSelect = ''
      document.body.style.cursor = ''
    }

    document.addEventListener('mousemove', onMouseMove)
    document.addEventListener('mouseup', onMouseUp)
    return () => {
      document.removeEventListener('mousemove', onMouseMove)
      document.removeEventListener('mouseup', onMouseUp)
    }
  }, [])

  const onHandleMouseDown = (e: React.MouseEvent) => {
    e.preventDefault()
    isDragging.current = true
    dragStartX.current = e.clientX
    dragStartWidth.current = width
    document.body.style.userSelect = 'none'
    document.body.style.cursor = 'ew-resize'
  }

  return (
    <>
      {/* Backdrop */}
      <div className="fixed inset-0 z-40" onClick={onClose} aria-hidden="true" />

      {/* Popup panel */}
      <div
        className="fixed top-0 right-0 h-screen z-50 flex flex-col bg-white"
        style={{
          width,
          borderLeft: '1px solid #111111',
          boxShadow: '-4px 0 20px rgba(0,0,0,0.12)',
        }}
        onClick={e => e.stopPropagation()}
      >
        {/* ── Drag handle ── thin strip on the left edge */}
        <div
          onMouseDown={onHandleMouseDown}
          style={{
            position: 'absolute',
            left: 0,
            top: 0,
            bottom: 0,
            width: 6,
            cursor: 'ew-resize',
            zIndex: 10,
            background: 'transparent',
            transition: 'background 0.15s',
          }}
          onMouseEnter={e => { (e.currentTarget as HTMLDivElement).style.background = 'rgba(0,0,0,0.12)' }}
          onMouseLeave={e => { (e.currentTarget as HTMLDivElement).style.background = 'transparent' }}
        />

        {/* Header */}
        <div
          className="flex items-start justify-between px-5 py-4 flex-shrink-0"
          style={{ borderBottom: '1px solid #111111' }}
        >
          <div className="pr-4">
            <p className="font-bold text-[#444444] leading-tight" style={{ fontSize: '1rem' }}>
              {title}
            </p>
            <p className="text-[#888888] mt-0.5" style={{ fontSize: '0.75rem', fontFamily: 'monospace' }}>
              {id}
            </p>
          </div>
          <button
            onClick={onClose}
            aria-label="Close code panel"
            className="flex-shrink-0 text-[#888888] hover:text-[#111111] transition-colors text-xl leading-none mt-0.5"
          >
            ×
          </button>
        </div>

        {/* White margin area containing the scrollable dark code box */}
        <div className="flex-1 flex flex-col overflow-hidden" style={{ padding: '1rem', minHeight: 0 }}>
          <div style={{ flex: 1, minHeight: 0, overflow: 'auto', background: '#000C18' }}>
            <SyntaxHighlighter
              language="haskell"
              style={abyssStyle}
              wrapLines={false}
              PreTag="div"
              customStyle={{ margin: 0, background: '#000C18', height: '100%' }}
            >
              {leanCode}
            </SyntaxHighlighter>
          </div>
        </div>
      </div>
    </>
  )
}
