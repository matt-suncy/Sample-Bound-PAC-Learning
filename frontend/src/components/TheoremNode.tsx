import { useState, memo } from 'react'
import { Handle, Position } from 'reactflow'
import type { NodeProps } from 'reactflow'
import type { TheoremNodeData } from '../data/graphData'
import MathText from './MathText'

// NODE_WIDTH must match the width used in DependencyGraph's dagre layout
export const NODE_WIDTH = 220
export const NODE_HEIGHT_COLLAPSED = 60

function TheoremNode({ data }: NodeProps<TheoremNodeData>) {
  const [hovered, setHovered] = useState(false)

  const bg = data.isHighlighted ? '#EEF3FF' : '#FFFFFF'

  return (
    <div
      onMouseEnter={() => setHovered(true)}
      onMouseLeave={() => setHovered(false)}
      style={{
        width: NODE_WIDTH,
        background: bg,
        border: '1px solid #111111',
        boxShadow: hovered
          ? '4px 4px 0 rgba(0,0,0,0.12)'
          : '3px 3px 0 rgba(0,0,0,0.08)',
        padding: '10px 12px',
        cursor: 'pointer',
        transition: 'box-shadow 0.15s ease',
        fontFamily: "'Cormorant Garamond', Georgia, serif",
        boxSizing: 'border-box',
      }}
    >
      <Handle
        type="target"
        position={Position.Bottom}
        style={{ background: '#111111', width: 6, height: 6, border: 'none' }}
      />

      {/* Title */}
      <p
        style={{
          margin: 0,
          fontSize: '0.8rem',
          fontWeight: 700,
          color: '#111111',
          lineHeight: 1.35,
          fontStyle: data.isPrivate ? 'italic' : 'normal',
          textAlign: 'center',
        }}
      >
        {data.label}
      </p>

      {/* File badge */}
      <p
        style={{
          margin: '4px 0 0',
          fontSize: '0.65rem',
          color: '#888888',
          textAlign: 'center',
          fontFamily: 'monospace',
        }}
      >
        {data.file}
      </p>

      {/* Natural language statement — shown on hover */}
      {hovered && (
        <MathText
          text={data.naturalLanguageStatement}
          style={{
            display: 'block',
            margin: '8px 0 0',
            fontSize: '0.75rem',
            color: '#444444',
            lineHeight: 1.55,
            textAlign: 'left',
            borderTop: '1px solid #e0e0e0',
            paddingTop: '6px',
          }}
        />
      )}

      <Handle
        type="source"
        position={Position.Top}
        style={{ background: '#111111', width: 6, height: 6, border: 'none' }}
      />
    </div>
  )
}

export default memo(TheoremNode)
